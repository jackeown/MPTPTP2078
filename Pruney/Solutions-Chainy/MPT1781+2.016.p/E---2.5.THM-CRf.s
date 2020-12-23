%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:11 EST 2020

% Result     : Theorem 0.43s
% Output     : CNFRefutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  179 (15828981 expanded)
%              Number of clauses        :  154 (5473061 expanded)
%              Number of leaves         :   12 (3959984 expanded)
%              Depth                    :   36
%              Number of atoms          :  707 (122889275 expanded)
%              Number of equality atoms :  186 (13664281 expanded)
%              Maximal formula depth    :   16 (   4 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).

fof(dt_k4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k4_tmap_1(X1,X2))
        & v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_grfunc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

fof(d9_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r2_funct_2(X1,X2,X3,X4)
          <=> ! [X5] :
                ( m1_subset_1(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).

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
    ! [X33,X34] :
      ( ( v1_funct_1(k4_tmap_1(X33,X34))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_pre_topc(X34,X33) )
      & ( v1_funct_2(k4_tmap_1(X33,X34),u1_struct_0(X34),u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_pre_topc(X34,X33) )
      & ( m1_subset_1(k4_tmap_1(X33,X34),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X33))))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_pre_topc(X34,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).

fof(c_0_14,negated_conjecture,(
    ! [X43] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
      & ( ~ m1_subset_1(X43,u1_struct_0(esk3_0))
        | ~ r2_hidden(X43,u1_struct_0(esk4_0))
        | X43 = k1_funct_1(esk5_0,X43) )
      & ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).

fof(c_0_15,plain,(
    ! [X20,X21,X22] :
      ( ( ~ v1_funct_2(X22,X20,X21)
        | X20 = k1_relset_1(X20,X21,X22)
        | X21 = k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( X20 != k1_relset_1(X20,X21,X22)
        | v1_funct_2(X22,X20,X21)
        | X21 = k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( ~ v1_funct_2(X22,X20,X21)
        | X20 = k1_relset_1(X20,X21,X22)
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( X20 != k1_relset_1(X20,X21,X22)
        | v1_funct_2(X22,X20,X21)
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( ~ v1_funct_2(X22,X20,X21)
        | X22 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( X22 != k1_xboole_0
        | v1_funct_2(X22,X20,X21)
        | X20 = k1_xboole_0
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | k1_relset_1(X17,X18,X19) = k1_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_23,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

fof(c_0_26,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_relat_1(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_27,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_30,plain,(
    ! [X29,X30,X31] :
      ( ( r1_tarski(k1_relat_1(X29),k1_relat_1(X30))
        | ~ r1_tarski(X29,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(X31,k1_relat_1(X29))
        | k1_funct_1(X29,X31) = k1_funct_1(X30,X31)
        | ~ r1_tarski(X29,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( r2_hidden(esk2_2(X29,X30),k1_relat_1(X29))
        | ~ r1_tarski(k1_relat_1(X29),k1_relat_1(X30))
        | r1_tarski(X29,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( k1_funct_1(X29,esk2_2(X29,X30)) != k1_funct_1(X30,esk2_2(X29,X30))
        | ~ r1_tarski(k1_relat_1(X29),k1_relat_1(X30))
        | r1_tarski(X29,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_grfunc_1])])])])])).

cnf(c_0_31,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0)) = u1_struct_0(esk4_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_33,plain,
    ( v1_funct_1(k4_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_37,plain,(
    ! [X35,X36] :
      ( ~ l1_pre_topc(X35)
      | ~ m1_pre_topc(X36,X35)
      | m1_subset_1(u1_struct_0(X36),k1_zfmisc_1(u1_struct_0(X35))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_38,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0) = u1_struct_0(esk4_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_28]),c_0_29])])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( k1_relat_1(k4_tmap_1(esk3_0,esk4_0)) = u1_struct_0(esk4_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_24])])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(k4_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_24]),c_0_35])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | m1_subset_1(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_45,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | r1_tarski(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( k1_relat_1(esk5_0) = u1_struct_0(esk4_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_38]),c_0_28])])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_35])])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_17]),c_0_18])])).

cnf(c_0_54,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),X1),u1_struct_0(esk4_0))
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | k1_funct_1(X1,esk2_2(X1,X2)) != k1_funct_1(X2,esk2_2(X1,X2))
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_56,plain,
    ( k1_funct_1(X2,X1) = k1_funct_1(X3,X1)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r1_tarski(X2,X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_57,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(X1,esk5_0),k1_relat_1(X1))
    | r1_tarski(X1,esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])])).

cnf(c_0_58,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_41]),c_0_42])])).

fof(c_0_59,plain,(
    ! [X37,X38,X39] :
      ( v2_struct_0(X37)
      | ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | v2_struct_0(X38)
      | ~ m1_pre_topc(X38,X37)
      | ~ m1_subset_1(X39,u1_struct_0(X37))
      | ~ r2_hidden(X39,u1_struct_0(X38))
      | k1_funct_1(k4_tmap_1(X37,X38),X39) = X39 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_47]),c_0_48]),c_0_49]),c_0_51])])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_47]),c_0_48]),c_0_49])])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(X1,k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(X1))
    | r1_tarski(X1,k4_tmap_1(esk3_0,esk4_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | k1_funct_1(X3,esk2_2(X1,X2)) != k1_funct_1(X2,esk2_2(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(esk2_2(X1,X2),k1_relat_1(X3))
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),k1_relat_1(k4_tmap_1(esk3_0,esk4_0)))
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_41]),c_0_42])])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_47]),c_0_48]),c_0_49])])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_funct_1(k4_tmap_1(X1,X2),X3) = X3
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | m1_subset_1(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_51]),c_0_48]),c_0_49])])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_47]),c_0_48]),c_0_49]),c_0_51])])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) != k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_48]),c_0_41]),c_0_49]),c_0_42]),c_0_51])])).

cnf(c_0_72,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(u1_struct_0(esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_51]),c_0_48]),c_0_49])])).

cnf(c_0_73,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,X1),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | u1_struct_0(esk3_0) = k1_xboole_0
    | v2_struct_0(X1)
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_74,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_75,negated_conjecture,
    ( X1 = k1_funct_1(esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_76,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(esk5_0))
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_69]),c_0_48]),c_0_49])])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | m1_subset_1(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk3_0))
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) != k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_40]),c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_61]),c_0_17])]),c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_61]),c_0_68])).

cnf(c_0_81,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) != k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))
    | ~ r1_tarski(k1_relat_1(esk5_0),k1_relat_1(k4_tmap_1(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_76]),c_0_41]),c_0_48]),c_0_42]),c_0_49]),c_0_51])])).

cnf(c_0_82,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,X1),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | u1_struct_0(esk3_0) = k1_xboole_0
    | v2_struct_0(X1)
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_77]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_83,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_84,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) != k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_40]),c_0_69])).

cnf(c_0_86,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_70]),c_0_17])]),c_0_74])).

cnf(c_0_87,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_70]),c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( k4_tmap_1(esk3_0,esk4_0) = esk5_0
    | u1_struct_0(esk3_0) = k1_xboole_0
    | ~ r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

fof(c_0_90,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( ~ r2_funct_2(X23,X24,X25,X26)
        | ~ m1_subset_1(X27,X23)
        | k1_funct_1(X25,X27) = k1_funct_1(X26,X27)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X23,X24)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( m1_subset_1(esk1_4(X23,X24,X25,X26),X23)
        | r2_funct_2(X23,X24,X25,X26)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X23,X24)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( k1_funct_1(X25,esk1_4(X23,X24,X25,X26)) != k1_funct_1(X26,esk1_4(X23,X24,X25,X26))
        | r2_funct_2(X23,X24,X25,X26)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X23,X24)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).

cnf(c_0_91,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_93,negated_conjecture,
    ( k4_tmap_1(esk3_0,esk4_0) = esk5_0
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,plain,
    ( r2_funct_2(X2,X3,X1,X4)
    | k1_funct_1(X1,esk1_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk1_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_95,plain,
    ( X1 = k1_relat_1(X2)
    | X1 != k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_97,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_94])).

cnf(c_0_98,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_99,negated_conjecture,
    ( k1_relat_1(k4_tmap_1(esk3_0,esk4_0)) = u1_struct_0(esk4_0)
    | u1_struct_0(esk4_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_24]),c_0_25])])).

cnf(c_0_100,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_48]),c_0_29]),c_0_28])])).

cnf(c_0_101,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | u1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_28]),c_0_29])])).

cnf(c_0_102,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1) = k1_funct_1(X2,X1)
    | u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r1_tarski(k4_tmap_1(esk3_0,esk4_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_99]),c_0_41]),c_0_42])])).

cnf(c_0_103,negated_conjecture,
    ( k1_relat_1(esk5_0) = u1_struct_0(esk4_0)
    | u1_struct_0(esk4_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_28]),c_0_29])])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_100])])).

cnf(c_0_106,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( k1_funct_1(X1,X2) = X2
    | u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,u1_struct_0(esk4_0))
    | ~ r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_102]),c_0_17]),c_0_18]),c_0_19])]),c_0_74]),c_0_20]),c_0_60])).

cnf(c_0_108,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,X1),u1_struct_0(esk4_0))
    | r1_tarski(esk5_0,X1)
    | u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_103]),c_0_48]),c_0_49])])).

cnf(c_0_109,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v1_funct_2(k4_tmap_1(esk3_0,esk4_0),k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_105])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(X1,k1_xboole_0)
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_100])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_100])).

cnf(c_0_113,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_100])).

cnf(c_0_114,negated_conjecture,
    ( k1_funct_1(X1,X2) = X2
    | esk5_0 = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_xboole_0)
    | ~ r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_107,c_0_105])).

cnf(c_0_115,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk2_2(esk5_0,X1),k1_xboole_0)
    | r1_tarski(esk5_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_105])).

cnf(c_0_116,negated_conjecture,
    ( k1_relat_1(k4_tmap_1(esk3_0,esk4_0)) = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_109]),c_0_110])).

cnf(c_0_117,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = X1
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_100]),c_0_111])).

cnf(c_0_118,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_112,c_0_105])).

cnf(c_0_119,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v1_funct_2(esk5_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_105])).

cnf(c_0_120,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1) = X1
    | esk5_0 = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_51]),c_0_41]),c_0_42])])).

cnf(c_0_121,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),k1_xboole_0)
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_41]),c_0_42]),c_0_51])])).

cnf(c_0_122,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = X1
    | esk5_0 = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_105])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))
    | u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_103]),c_0_48]),c_0_49])])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk5_0),k1_relat_1(X1))
    | r1_tarski(X1,esk5_0)
    | u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_103]),c_0_48]),c_0_49])])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1))
    | u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_103]),c_0_48]),c_0_49])])).

cnf(c_0_126,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_118]),c_0_119])).

cnf(c_0_127,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | esk5_0 = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_128,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | esk5_0 = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_122,c_0_121])).

cnf(c_0_129,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_123,c_0_105])).

cnf(c_0_130,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk2_2(X1,esk5_0),k1_relat_1(X1))
    | r1_tarski(X1,esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_105])).

cnf(c_0_131,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(u1_struct_0(esk4_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_48]),c_0_49]),c_0_51])]),c_0_105])).

cnf(c_0_132,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | ~ r1_tarski(k1_relat_1(esk5_0),k1_relat_1(k4_tmap_1(esk3_0,esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_127]),c_0_41]),c_0_48]),c_0_42]),c_0_49])]),c_0_128])).

cnf(c_0_133,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(k1_relat_1(esk5_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_51]),c_0_48]),c_0_49])])).

cnf(c_0_134,negated_conjecture,
    ( r1_tarski(X1,X2)
    | k1_funct_1(esk5_0,esk2_2(X1,X2)) != k1_funct_1(X2,esk2_2(X1,X2))
    | u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),u1_struct_0(esk4_0))
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_103]),c_0_48]),c_0_49])])).

cnf(c_0_135,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_99]),c_0_41]),c_0_42])]),c_0_131]),c_0_105])).

cnf(c_0_136,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_116]),c_0_133])).

cnf(c_0_137,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_125,c_0_105])).

cnf(c_0_138,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_48]),c_0_41]),c_0_49]),c_0_42])]),c_0_136]),c_0_105])).

cnf(c_0_139,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_51]),c_0_48]),c_0_49])])).

cnf(c_0_140,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_116]),c_0_139])).

cnf(c_0_141,negated_conjecture,
    ( k4_tmap_1(esk3_0,esk4_0) = k1_xboole_0
    | u1_struct_0(esk4_0) = k1_xboole_0
    | u1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_24]),c_0_25])])).

cnf(c_0_142,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),k1_xboole_0,k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_92,c_0_100])).

cnf(c_0_143,negated_conjecture,
    ( k4_tmap_1(esk3_0,esk4_0) = esk5_0
    | esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_140]),c_0_136])).

cnf(c_0_144,negated_conjecture,
    ( k4_tmap_1(esk3_0,esk4_0) = k1_xboole_0
    | u1_struct_0(esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_141,c_0_100])])).

cnf(c_0_145,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk4_0),k1_xboole_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_142,c_0_143])).

cnf(c_0_146,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk4_0),k1_xboole_0,k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_142,c_0_144])).

cnf(c_0_147,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_97]),c_0_48]),c_0_113]),c_0_112])])).

cnf(c_0_148,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk4_0),k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_149,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_147])).

cnf(c_0_150,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_113,c_0_147])).

cnf(c_0_151,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_112,c_0_147])).

cnf(c_0_152,negated_conjecture,
    ( r1_tarski(X1,X2)
    | k1_funct_1(X2,esk2_2(X1,X2)) != esk2_2(X1,X2)
    | u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),u1_struct_0(esk4_0))
    | ~ r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_107])).

cnf(c_0_153,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = k1_funct_1(X2,X1)
    | u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r1_tarski(esk5_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_103]),c_0_48]),c_0_49])])).

cnf(c_0_154,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,X1) = X1
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_117,c_0_147])).

cnf(c_0_155,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_97]),c_0_149]),c_0_150]),c_0_151])])).

cnf(c_0_156,negated_conjecture,
    ( r1_tarski(X1,X2)
    | k1_funct_1(X1,esk2_2(X1,X2)) != esk2_2(X1,X2)
    | u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),u1_struct_0(esk4_0))
    | ~ r1_tarski(k4_tmap_1(esk3_0,esk4_0),X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_107])).

cnf(c_0_157,negated_conjecture,
    ( r1_tarski(X1,X2)
    | k1_funct_1(esk5_0,esk2_2(X1,X2)) != esk2_2(X1,X2)
    | u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),u1_struct_0(esk4_0))
    | ~ r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_152,c_0_153])).

cnf(c_0_158,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,X1) = X1
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_154,c_0_155])).

cnf(c_0_159,negated_conjecture,
    ( r2_hidden(esk2_2(X1,k1_xboole_0),k1_relat_1(X1))
    | r1_tarski(X1,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_147]),c_0_147]),c_0_155]),c_0_155])])).

cnf(c_0_160,negated_conjecture,
    ( k1_relat_1(k4_tmap_1(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_155]),c_0_155])])).

cnf(c_0_161,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = u1_struct_0(esk4_0)
    | u1_struct_0(esk4_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_103,c_0_147])).

cnf(c_0_162,negated_conjecture,
    ( r1_tarski(X1,X2)
    | k1_funct_1(esk5_0,esk2_2(X1,X2)) != esk2_2(X1,X2)
    | u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),u1_struct_0(esk4_0))
    | ~ r1_tarski(k4_tmap_1(esk3_0,esk4_0),X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_156,c_0_153])).

cnf(c_0_163,negated_conjecture,
    ( r2_hidden(esk2_2(k1_xboole_0,X1),k1_xboole_0)
    | r1_tarski(k1_xboole_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_147]),c_0_147]),c_0_155]),c_0_155]),c_0_155])])).

cnf(c_0_164,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),k1_xboole_0)
    | ~ r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(k1_xboole_0,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_157,c_0_147]),c_0_147]),c_0_155]),c_0_155])]),c_0_158])).

cnf(c_0_165,negated_conjecture,
    ( r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),k1_xboole_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_160]),c_0_41]),c_0_42]),c_0_51])])).

cnf(c_0_166,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_147])).

cnf(c_0_167,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_161,c_0_155]),c_0_155])])).

cnf(c_0_168,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),k1_xboole_0)
    | ~ r1_tarski(k4_tmap_1(esk3_0,esk4_0),X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_162,c_0_147]),c_0_147]),c_0_155]),c_0_155])]),c_0_158])).

cnf(c_0_169,negated_conjecture,
    ( r2_hidden(esk2_2(k1_xboole_0,k4_tmap_1(esk3_0,esk4_0)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_160]),c_0_41]),c_0_42]),c_0_51])])).

cnf(c_0_170,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),k1_xboole_0,k4_tmap_1(esk3_0,esk4_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_142,c_0_147])).

cnf(c_0_171,negated_conjecture,
    ( r1_tarski(k4_tmap_1(esk3_0,esk4_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_165]),c_0_149]),c_0_41]),c_0_166]),c_0_42]),c_0_51]),c_0_160]),c_0_167]),c_0_51]),c_0_51])])).

cnf(c_0_172,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_169]),c_0_41]),c_0_149]),c_0_42]),c_0_166]),c_0_51]),c_0_167]),c_0_160]),c_0_51]),c_0_51])])).

cnf(c_0_173,negated_conjecture,
    ( ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1(esk3_0,esk4_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_170,c_0_155])).

cnf(c_0_174,negated_conjecture,
    ( k4_tmap_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_171]),c_0_172])])).

cnf(c_0_175,negated_conjecture,
    ( ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_173,c_0_174])).

cnf(c_0_176,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_150,c_0_155])).

cnf(c_0_177,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_151,c_0_155])).

cnf(c_0_178,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_97]),c_0_149]),c_0_176]),c_0_177])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.43/0.60  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.43/0.60  # and selection function PSelectComplexExceptRRHorn.
% 0.43/0.60  #
% 0.43/0.60  # Preprocessing time       : 0.042 s
% 0.43/0.60  # Presaturation interreduction done
% 0.43/0.60  
% 0.43/0.60  # Proof found!
% 0.43/0.60  # SZS status Theorem
% 0.43/0.60  # SZS output start CNFRefutation
% 0.43/0.60  fof(t96_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 0.43/0.60  fof(dt_k4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k4_tmap_1(X1,X2))&v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 0.43/0.60  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.43/0.60  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.43/0.60  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.43/0.60  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.43/0.60  fof(t8_grfunc_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,X2)<=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_grfunc_1)).
% 0.43/0.60  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.43/0.60  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.43/0.60  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.43/0.60  fof(t95_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,u1_struct_0(X2))=>k1_funct_1(k4_tmap_1(X1,X2),X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 0.43/0.60  fof(d9_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_2)).
% 0.43/0.60  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t96_tmap_1])).
% 0.43/0.60  fof(c_0_13, plain, ![X33, X34]:(((v1_funct_1(k4_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33)))&(v1_funct_2(k4_tmap_1(X33,X34),u1_struct_0(X34),u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33))))&(m1_subset_1(k4_tmap_1(X33,X34),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X33))))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).
% 0.43/0.60  fof(c_0_14, negated_conjecture, ![X43]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))))&((~m1_subset_1(X43,u1_struct_0(esk3_0))|(~r2_hidden(X43,u1_struct_0(esk4_0))|X43=k1_funct_1(esk5_0,X43)))&~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).
% 0.43/0.60  fof(c_0_15, plain, ![X20, X21, X22]:((((~v1_funct_2(X22,X20,X21)|X20=k1_relset_1(X20,X21,X22)|X21=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(X20!=k1_relset_1(X20,X21,X22)|v1_funct_2(X22,X20,X21)|X21=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))&((~v1_funct_2(X22,X20,X21)|X20=k1_relset_1(X20,X21,X22)|X20!=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(X20!=k1_relset_1(X20,X21,X22)|v1_funct_2(X22,X20,X21)|X20!=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))))&((~v1_funct_2(X22,X20,X21)|X22=k1_xboole_0|X20=k1_xboole_0|X21!=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(X22!=k1_xboole_0|v1_funct_2(X22,X20,X21)|X20=k1_xboole_0|X21!=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.43/0.60  cnf(c_0_16, plain, (m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.43/0.60  cnf(c_0_17, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.60  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.60  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.60  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.60  cnf(c_0_21, plain, (v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.43/0.60  fof(c_0_22, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|k1_relset_1(X17,X18,X19)=k1_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.43/0.60  cnf(c_0_23, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.43/0.60  cnf(c_0_24, negated_conjecture, (m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.43/0.60  cnf(c_0_25, negated_conjecture, (v1_funct_2(k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.43/0.60  fof(c_0_26, plain, ![X13, X14]:(~v1_relat_1(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_relat_1(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.43/0.60  fof(c_0_27, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.43/0.60  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.60  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.60  fof(c_0_30, plain, ![X29, X30, X31]:(((r1_tarski(k1_relat_1(X29),k1_relat_1(X30))|~r1_tarski(X29,X30)|(~v1_relat_1(X30)|~v1_funct_1(X30))|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(~r2_hidden(X31,k1_relat_1(X29))|k1_funct_1(X29,X31)=k1_funct_1(X30,X31)|~r1_tarski(X29,X30)|(~v1_relat_1(X30)|~v1_funct_1(X30))|(~v1_relat_1(X29)|~v1_funct_1(X29))))&((r2_hidden(esk2_2(X29,X30),k1_relat_1(X29))|~r1_tarski(k1_relat_1(X29),k1_relat_1(X30))|r1_tarski(X29,X30)|(~v1_relat_1(X30)|~v1_funct_1(X30))|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(k1_funct_1(X29,esk2_2(X29,X30))!=k1_funct_1(X30,esk2_2(X29,X30))|~r1_tarski(k1_relat_1(X29),k1_relat_1(X30))|r1_tarski(X29,X30)|(~v1_relat_1(X30)|~v1_funct_1(X30))|(~v1_relat_1(X29)|~v1_funct_1(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_grfunc_1])])])])])).
% 0.43/0.60  cnf(c_0_31, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.43/0.60  cnf(c_0_32, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0))=u1_struct_0(esk4_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.43/0.60  cnf(c_0_33, plain, (v1_funct_1(k4_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.43/0.60  cnf(c_0_34, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.43/0.60  cnf(c_0_35, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.43/0.60  fof(c_0_36, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.43/0.60  fof(c_0_37, plain, ![X35, X36]:(~l1_pre_topc(X35)|(~m1_pre_topc(X36,X35)|m1_subset_1(u1_struct_0(X36),k1_zfmisc_1(u1_struct_0(X35))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.43/0.60  cnf(c_0_38, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0)=u1_struct_0(esk4_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_28]), c_0_29])])).
% 0.43/0.60  cnf(c_0_39, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.43/0.60  cnf(c_0_40, negated_conjecture, (k1_relat_1(k4_tmap_1(esk3_0,esk4_0))=u1_struct_0(esk4_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_24])])).
% 0.43/0.60  cnf(c_0_41, negated_conjecture, (v1_funct_1(k4_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.43/0.60  cnf(c_0_42, negated_conjecture, (v1_relat_1(k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_24]), c_0_35])])).
% 0.43/0.60  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.43/0.60  fof(c_0_44, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|m1_subset_1(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.43/0.60  cnf(c_0_45, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.43/0.60  cnf(c_0_46, plain, (r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))|r1_tarski(X1,X2)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.43/0.60  cnf(c_0_47, negated_conjecture, (k1_relat_1(esk5_0)=u1_struct_0(esk4_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_38]), c_0_28])])).
% 0.43/0.60  cnf(c_0_48, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.60  cnf(c_0_49, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_28]), c_0_35])])).
% 0.43/0.60  cnf(c_0_50, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X1,k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42])])).
% 0.43/0.60  cnf(c_0_51, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_43])).
% 0.43/0.60  cnf(c_0_52, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.43/0.60  cnf(c_0_53, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_17]), c_0_18])])).
% 0.43/0.60  cnf(c_0_54, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),X1),u1_struct_0(esk4_0))|r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_40]), c_0_41]), c_0_42])])).
% 0.43/0.60  cnf(c_0_55, plain, (r1_tarski(X1,X2)|k1_funct_1(X1,esk2_2(X1,X2))!=k1_funct_1(X2,esk2_2(X1,X2))|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.43/0.60  cnf(c_0_56, plain, (k1_funct_1(X2,X1)=k1_funct_1(X3,X1)|~r2_hidden(X1,k1_relat_1(X2))|~r1_tarski(X2,X3)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.43/0.60  cnf(c_0_57, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(X1,esk5_0),k1_relat_1(X1))|r1_tarski(X1,esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49])])).
% 0.43/0.60  cnf(c_0_58, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k1_relat_1(k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_41]), c_0_42])])).
% 0.43/0.60  fof(c_0_59, plain, ![X37, X38, X39]:(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|(v2_struct_0(X38)|~m1_pre_topc(X38,X37)|(~m1_subset_1(X39,u1_struct_0(X37))|(~r2_hidden(X39,u1_struct_0(X38))|k1_funct_1(k4_tmap_1(X37,X38),X39)=X39)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).
% 0.43/0.60  cnf(c_0_60, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.43/0.60  cnf(c_0_61, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_47]), c_0_48]), c_0_49]), c_0_51])])).
% 0.43/0.60  cnf(c_0_62, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_47]), c_0_48]), c_0_49])])).
% 0.43/0.60  cnf(c_0_63, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(X1,k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(X1))|r1_tarski(X1,k4_tmap_1(esk3_0,esk4_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_40]), c_0_41]), c_0_42])])).
% 0.43/0.60  cnf(c_0_64, plain, (r1_tarski(X1,X2)|k1_funct_1(X3,esk2_2(X1,X2))!=k1_funct_1(X2,esk2_2(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X3)|~r2_hidden(esk2_2(X1,X2),k1_relat_1(X3))|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.43/0.60  cnf(c_0_65, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),k1_relat_1(k4_tmap_1(esk3_0,esk4_0)))|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_41]), c_0_42])])).
% 0.43/0.60  cnf(c_0_66, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_47]), c_0_48]), c_0_49])])).
% 0.43/0.60  cnf(c_0_67, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_funct_1(k4_tmap_1(X1,X2),X3)=X3|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.43/0.60  cnf(c_0_68, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|m1_subset_1(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.43/0.60  cnf(c_0_69, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k1_relat_1(esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_51]), c_0_48]), c_0_49])])).
% 0.43/0.60  cnf(c_0_70, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_47]), c_0_48]), c_0_49]), c_0_51])])).
% 0.43/0.60  cnf(c_0_71, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)|k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))!=k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))|~r1_tarski(k1_relat_1(k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_48]), c_0_41]), c_0_49]), c_0_42]), c_0_51])])).
% 0.43/0.60  cnf(c_0_72, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(u1_struct_0(esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_51]), c_0_48]), c_0_49])])).
% 0.43/0.60  cnf(c_0_73, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,X1),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)|u1_struct_0(esk3_0)=k1_xboole_0|v2_struct_0(X1)|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)|~m1_pre_topc(X1,esk3_0)|~r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_18]), c_0_19])]), c_0_20])).
% 0.43/0.60  cnf(c_0_74, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.60  cnf(c_0_75, negated_conjecture, (X1=k1_funct_1(esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.60  cnf(c_0_76, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(esk5_0))|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_69]), c_0_48]), c_0_49])])).
% 0.43/0.60  cnf(c_0_77, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|m1_subset_1(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk3_0))|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_70])).
% 0.43/0.60  cnf(c_0_78, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)|k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))!=k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_40]), c_0_72])).
% 0.43/0.60  cnf(c_0_79, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)|u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_61]), c_0_17])]), c_0_74])).
% 0.43/0.60  cnf(c_0_80, negated_conjecture, (k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)|u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_61]), c_0_68])).
% 0.43/0.60  cnf(c_0_81, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))|k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))!=k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))|~r1_tarski(k1_relat_1(esk5_0),k1_relat_1(k4_tmap_1(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_76]), c_0_41]), c_0_48]), c_0_42]), c_0_49]), c_0_51])])).
% 0.43/0.60  cnf(c_0_82, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,X1),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))|u1_struct_0(esk3_0)=k1_xboole_0|v2_struct_0(X1)|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(X1,esk3_0)|~r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_77]), c_0_18]), c_0_19])]), c_0_20])).
% 0.43/0.60  cnf(c_0_83, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.43/0.60  cnf(c_0_84, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.43/0.60  cnf(c_0_85, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))|k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))!=k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_40]), c_0_69])).
% 0.43/0.60  cnf(c_0_86, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))|u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_70]), c_0_17])]), c_0_74])).
% 0.43/0.60  cnf(c_0_87, negated_conjecture, (k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))|u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_70]), c_0_77])).
% 0.43/0.60  cnf(c_0_88, negated_conjecture, (k4_tmap_1(esk3_0,esk4_0)=esk5_0|u1_struct_0(esk3_0)=k1_xboole_0|~r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.43/0.60  cnf(c_0_89, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87])).
% 0.43/0.60  fof(c_0_90, plain, ![X23, X24, X25, X26, X27]:((~r2_funct_2(X23,X24,X25,X26)|(~m1_subset_1(X27,X23)|k1_funct_1(X25,X27)=k1_funct_1(X26,X27))|(~v1_funct_1(X26)|~v1_funct_2(X26,X23,X24)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))|(~v1_funct_1(X25)|~v1_funct_2(X25,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))&((m1_subset_1(esk1_4(X23,X24,X25,X26),X23)|r2_funct_2(X23,X24,X25,X26)|(~v1_funct_1(X26)|~v1_funct_2(X26,X23,X24)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))|(~v1_funct_1(X25)|~v1_funct_2(X25,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))&(k1_funct_1(X25,esk1_4(X23,X24,X25,X26))!=k1_funct_1(X26,esk1_4(X23,X24,X25,X26))|r2_funct_2(X23,X24,X25,X26)|(~v1_funct_1(X26)|~v1_funct_2(X26,X23,X24)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))|(~v1_funct_1(X25)|~v1_funct_2(X25,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).
% 0.43/0.60  cnf(c_0_91, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.43/0.60  cnf(c_0_92, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.60  cnf(c_0_93, negated_conjecture, (k4_tmap_1(esk3_0,esk4_0)=esk5_0|u1_struct_0(esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.43/0.60  cnf(c_0_94, plain, (r2_funct_2(X2,X3,X1,X4)|k1_funct_1(X1,esk1_4(X2,X3,X1,X4))!=k1_funct_1(X4,esk1_4(X2,X3,X1,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.43/0.60  cnf(c_0_95, plain, (X1=k1_relat_1(X2)|X1!=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_31, c_0_91])).
% 0.43/0.60  cnf(c_0_96, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.43/0.60  cnf(c_0_97, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_94])).
% 0.43/0.60  cnf(c_0_98, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.43/0.60  cnf(c_0_99, negated_conjecture, (k1_relat_1(k4_tmap_1(esk3_0,esk4_0))=u1_struct_0(esk4_0)|u1_struct_0(esk4_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_24]), c_0_25])])).
% 0.43/0.60  cnf(c_0_100, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_48]), c_0_29]), c_0_28])])).
% 0.43/0.60  cnf(c_0_101, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|esk5_0=k1_xboole_0|u1_struct_0(esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_28]), c_0_29])])).
% 0.43/0.60  cnf(c_0_102, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)=k1_funct_1(X2,X1)|u1_struct_0(esk4_0)!=k1_xboole_0|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,u1_struct_0(esk4_0))|~r1_tarski(k4_tmap_1(esk3_0,esk4_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_99]), c_0_41]), c_0_42])])).
% 0.43/0.60  cnf(c_0_103, negated_conjecture, (k1_relat_1(esk5_0)=u1_struct_0(esk4_0)|u1_struct_0(esk4_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_28]), c_0_29])])).
% 0.43/0.60  cnf(c_0_104, negated_conjecture, (m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),k1_xboole_0)))), inference(rw,[status(thm)],[c_0_24, c_0_100])).
% 0.43/0.60  cnf(c_0_105, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_100])])).
% 0.43/0.60  cnf(c_0_106, negated_conjecture, (v1_funct_2(k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_25, c_0_100])).
% 0.43/0.60  cnf(c_0_107, negated_conjecture, (k1_funct_1(X1,X2)=X2|u1_struct_0(esk4_0)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,u1_struct_0(esk4_0))|~r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_102]), c_0_17]), c_0_18]), c_0_19])]), c_0_74]), c_0_20]), c_0_60])).
% 0.43/0.60  cnf(c_0_108, negated_conjecture, (r2_hidden(esk2_2(esk5_0,X1),u1_struct_0(esk4_0))|r1_tarski(esk5_0,X1)|u1_struct_0(esk4_0)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_103]), c_0_48]), c_0_49])])).
% 0.43/0.60  cnf(c_0_109, negated_conjecture, (esk5_0=k1_xboole_0|m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.43/0.60  cnf(c_0_110, negated_conjecture, (esk5_0=k1_xboole_0|v1_funct_2(k4_tmap_1(esk3_0,esk4_0),k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_106, c_0_105])).
% 0.43/0.60  cnf(c_0_111, negated_conjecture, (m1_subset_1(X1,k1_xboole_0)|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_60, c_0_100])).
% 0.43/0.60  cnf(c_0_112, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),k1_xboole_0)))), inference(rw,[status(thm)],[c_0_28, c_0_100])).
% 0.43/0.60  cnf(c_0_113, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk4_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_29, c_0_100])).
% 0.43/0.60  cnf(c_0_114, negated_conjecture, (k1_funct_1(X1,X2)=X2|esk5_0=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_xboole_0)|~r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_107, c_0_105])).
% 0.43/0.60  cnf(c_0_115, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk2_2(esk5_0,X1),k1_xboole_0)|r1_tarski(esk5_0,X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_xboole_0,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_108, c_0_105])).
% 0.43/0.60  cnf(c_0_116, negated_conjecture, (k1_relat_1(k4_tmap_1(esk3_0,esk4_0))=k1_xboole_0|esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_109]), c_0_110])).
% 0.43/0.60  cnf(c_0_117, negated_conjecture, (k1_funct_1(esk5_0,X1)=X1|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_100]), c_0_111])).
% 0.43/0.60  cnf(c_0_118, negated_conjecture, (esk5_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_112, c_0_105])).
% 0.43/0.60  cnf(c_0_119, negated_conjecture, (esk5_0=k1_xboole_0|v1_funct_2(esk5_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_113, c_0_105])).
% 0.43/0.60  cnf(c_0_120, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)=X1|esk5_0=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_51]), c_0_41]), c_0_42])])).
% 0.43/0.60  cnf(c_0_121, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),k1_xboole_0)|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_41]), c_0_42]), c_0_51])])).
% 0.43/0.60  cnf(c_0_122, negated_conjecture, (k1_funct_1(esk5_0,X1)=X1|esk5_0=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_117, c_0_105])).
% 0.43/0.60  cnf(c_0_123, negated_conjecture, (r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))|u1_struct_0(esk4_0)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_103]), c_0_48]), c_0_49])])).
% 0.43/0.60  cnf(c_0_124, negated_conjecture, (r2_hidden(esk2_2(X1,esk5_0),k1_relat_1(X1))|r1_tarski(X1,esk5_0)|u1_struct_0(esk4_0)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_103]), c_0_48]), c_0_49])])).
% 0.43/0.60  cnf(c_0_125, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1))|u1_struct_0(esk4_0)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_103]), c_0_48]), c_0_49])])).
% 0.43/0.60  cnf(c_0_126, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_118]), c_0_119])).
% 0.43/0.60  cnf(c_0_127, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))|esk5_0=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 0.43/0.60  cnf(c_0_128, negated_conjecture, (k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))|esk5_0=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_122, c_0_121])).
% 0.43/0.60  cnf(c_0_129, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(k1_relat_1(X1),k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_123, c_0_105])).
% 0.43/0.60  cnf(c_0_130, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk2_2(X1,esk5_0),k1_relat_1(X1))|r1_tarski(X1,esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_124, c_0_105])).
% 0.43/0.60  cnf(c_0_131, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(u1_struct_0(esk4_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_48]), c_0_49]), c_0_51])]), c_0_105])).
% 0.43/0.60  cnf(c_0_132, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))|~r1_tarski(k1_relat_1(esk5_0),k1_relat_1(k4_tmap_1(esk3_0,esk4_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_127]), c_0_41]), c_0_48]), c_0_42]), c_0_49])]), c_0_128])).
% 0.43/0.60  cnf(c_0_133, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(k1_relat_1(esk5_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_51]), c_0_48]), c_0_49])])).
% 0.43/0.60  cnf(c_0_134, negated_conjecture, (r1_tarski(X1,X2)|k1_funct_1(esk5_0,esk2_2(X1,X2))!=k1_funct_1(X2,esk2_2(X1,X2))|u1_struct_0(esk4_0)!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(esk2_2(X1,X2),u1_struct_0(esk4_0))|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_103]), c_0_48]), c_0_49])])).
% 0.43/0.60  cnf(c_0_135, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_99]), c_0_41]), c_0_42])]), c_0_131]), c_0_105])).
% 0.43/0.60  cnf(c_0_136, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_116]), c_0_133])).
% 0.43/0.60  cnf(c_0_137, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(k1_xboole_0,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_125, c_0_105])).
% 0.43/0.60  cnf(c_0_138, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)|~r1_tarski(k1_relat_1(k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_48]), c_0_41]), c_0_49]), c_0_42])]), c_0_136]), c_0_105])).
% 0.43/0.60  cnf(c_0_139, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(k1_xboole_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_51]), c_0_48]), c_0_49])])).
% 0.43/0.60  cnf(c_0_140, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_116]), c_0_139])).
% 0.43/0.60  cnf(c_0_141, negated_conjecture, (k4_tmap_1(esk3_0,esk4_0)=k1_xboole_0|u1_struct_0(esk4_0)=k1_xboole_0|u1_struct_0(esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_24]), c_0_25])])).
% 0.43/0.60  cnf(c_0_142, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),k1_xboole_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_92, c_0_100])).
% 0.43/0.60  cnf(c_0_143, negated_conjecture, (k4_tmap_1(esk3_0,esk4_0)=esk5_0|esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_140]), c_0_136])).
% 0.43/0.60  cnf(c_0_144, negated_conjecture, (k4_tmap_1(esk3_0,esk4_0)=k1_xboole_0|u1_struct_0(esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_141, c_0_100])])).
% 0.43/0.60  cnf(c_0_145, negated_conjecture, (esk5_0=k1_xboole_0|~r2_funct_2(u1_struct_0(esk4_0),k1_xboole_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_142, c_0_143])).
% 0.43/0.60  cnf(c_0_146, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|~r2_funct_2(u1_struct_0(esk4_0),k1_xboole_0,k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_142, c_0_144])).
% 0.43/0.60  cnf(c_0_147, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_97]), c_0_48]), c_0_113]), c_0_112])])).
% 0.43/0.60  cnf(c_0_148, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|~r2_funct_2(u1_struct_0(esk4_0),k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_146, c_0_147])).
% 0.43/0.60  cnf(c_0_149, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_48, c_0_147])).
% 0.43/0.60  cnf(c_0_150, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_113, c_0_147])).
% 0.43/0.60  cnf(c_0_151, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),k1_xboole_0)))), inference(rw,[status(thm)],[c_0_112, c_0_147])).
% 0.43/0.60  cnf(c_0_152, negated_conjecture, (r1_tarski(X1,X2)|k1_funct_1(X2,esk2_2(X1,X2))!=esk2_2(X1,X2)|u1_struct_0(esk4_0)!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(esk2_2(X1,X2),u1_struct_0(esk4_0))|~r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_55, c_0_107])).
% 0.43/0.60  cnf(c_0_153, negated_conjecture, (k1_funct_1(esk5_0,X1)=k1_funct_1(X2,X1)|u1_struct_0(esk4_0)!=k1_xboole_0|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,u1_struct_0(esk4_0))|~r1_tarski(esk5_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_103]), c_0_48]), c_0_49])])).
% 0.43/0.60  cnf(c_0_154, negated_conjecture, (k1_funct_1(k1_xboole_0,X1)=X1|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_117, c_0_147])).
% 0.43/0.60  cnf(c_0_155, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_97]), c_0_149]), c_0_150]), c_0_151])])).
% 0.43/0.60  cnf(c_0_156, negated_conjecture, (r1_tarski(X1,X2)|k1_funct_1(X1,esk2_2(X1,X2))!=esk2_2(X1,X2)|u1_struct_0(esk4_0)!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(esk2_2(X1,X2),u1_struct_0(esk4_0))|~r1_tarski(k4_tmap_1(esk3_0,esk4_0),X2)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_55, c_0_107])).
% 0.43/0.60  cnf(c_0_157, negated_conjecture, (r1_tarski(X1,X2)|k1_funct_1(esk5_0,esk2_2(X1,X2))!=esk2_2(X1,X2)|u1_struct_0(esk4_0)!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(esk2_2(X1,X2),u1_struct_0(esk4_0))|~r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(esk5_0,X2)), inference(spm,[status(thm)],[c_0_152, c_0_153])).
% 0.43/0.60  cnf(c_0_158, negated_conjecture, (k1_funct_1(k1_xboole_0,X1)=X1|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_154, c_0_155])).
% 0.43/0.60  cnf(c_0_159, negated_conjecture, (r2_hidden(esk2_2(X1,k1_xboole_0),k1_relat_1(X1))|r1_tarski(X1,k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_147]), c_0_147]), c_0_155]), c_0_155])])).
% 0.43/0.60  cnf(c_0_160, negated_conjecture, (k1_relat_1(k4_tmap_1(esk3_0,esk4_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_155]), c_0_155])])).
% 0.43/0.60  cnf(c_0_161, negated_conjecture, (k1_relat_1(k1_xboole_0)=u1_struct_0(esk4_0)|u1_struct_0(esk4_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_103, c_0_147])).
% 0.43/0.60  cnf(c_0_162, negated_conjecture, (r1_tarski(X1,X2)|k1_funct_1(esk5_0,esk2_2(X1,X2))!=esk2_2(X1,X2)|u1_struct_0(esk4_0)!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(esk2_2(X1,X2),u1_struct_0(esk4_0))|~r1_tarski(k4_tmap_1(esk3_0,esk4_0),X2)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_156, c_0_153])).
% 0.43/0.60  cnf(c_0_163, negated_conjecture, (r2_hidden(esk2_2(k1_xboole_0,X1),k1_xboole_0)|r1_tarski(k1_xboole_0,X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_xboole_0,k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_147]), c_0_147]), c_0_155]), c_0_155]), c_0_155])])).
% 0.43/0.60  cnf(c_0_164, negated_conjecture, (r1_tarski(X1,X2)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(esk2_2(X1,X2),k1_xboole_0)|~r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(k1_xboole_0,X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_157, c_0_147]), c_0_147]), c_0_155]), c_0_155])]), c_0_158])).
% 0.43/0.60  cnf(c_0_165, negated_conjecture, (r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),k1_xboole_0),k1_xboole_0)|r1_tarski(k4_tmap_1(esk3_0,esk4_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_160]), c_0_41]), c_0_42]), c_0_51])])).
% 0.43/0.60  cnf(c_0_166, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_49, c_0_147])).
% 0.43/0.60  cnf(c_0_167, negated_conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_161, c_0_155]), c_0_155])])).
% 0.43/0.60  cnf(c_0_168, negated_conjecture, (r1_tarski(X1,X2)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(esk2_2(X1,X2),k1_xboole_0)|~r1_tarski(k4_tmap_1(esk3_0,esk4_0),X2)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(k1_xboole_0,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_162, c_0_147]), c_0_147]), c_0_155]), c_0_155])]), c_0_158])).
% 0.43/0.60  cnf(c_0_169, negated_conjecture, (r2_hidden(esk2_2(k1_xboole_0,k4_tmap_1(esk3_0,esk4_0)),k1_xboole_0)|r1_tarski(k1_xboole_0,k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_160]), c_0_41]), c_0_42]), c_0_51])])).
% 0.43/0.60  cnf(c_0_170, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),k1_xboole_0,k4_tmap_1(esk3_0,esk4_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_142, c_0_147])).
% 0.43/0.60  cnf(c_0_171, negated_conjecture, (r1_tarski(k4_tmap_1(esk3_0,esk4_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_165]), c_0_149]), c_0_41]), c_0_166]), c_0_42]), c_0_51]), c_0_160]), c_0_167]), c_0_51]), c_0_51])])).
% 0.43/0.60  cnf(c_0_172, negated_conjecture, (r1_tarski(k1_xboole_0,k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_169]), c_0_41]), c_0_149]), c_0_42]), c_0_166]), c_0_51]), c_0_167]), c_0_160]), c_0_51]), c_0_51])])).
% 0.43/0.60  cnf(c_0_173, negated_conjecture, (~r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1(esk3_0,esk4_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_170, c_0_155])).
% 0.43/0.60  cnf(c_0_174, negated_conjecture, (k4_tmap_1(esk3_0,esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_171]), c_0_172])])).
% 0.43/0.60  cnf(c_0_175, negated_conjecture, (~r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_173, c_0_174])).
% 0.43/0.60  cnf(c_0_176, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_150, c_0_155])).
% 0.43/0.60  cnf(c_0_177, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_151, c_0_155])).
% 0.43/0.60  cnf(c_0_178, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_97]), c_0_149]), c_0_176]), c_0_177])]), ['proof']).
% 0.43/0.60  # SZS output end CNFRefutation
% 0.43/0.60  # Proof object total steps             : 179
% 0.43/0.60  # Proof object clause steps            : 154
% 0.43/0.60  # Proof object formula steps           : 25
% 0.43/0.60  # Proof object conjectures             : 134
% 0.43/0.60  # Proof object clause conjectures      : 131
% 0.43/0.60  # Proof object formula conjectures     : 3
% 0.43/0.60  # Proof object initial clauses used    : 29
% 0.43/0.60  # Proof object initial formulas used   : 12
% 0.43/0.60  # Proof object generating inferences   : 96
% 0.43/0.60  # Proof object simplifying inferences  : 277
% 0.43/0.60  # Training examples: 0 positive, 0 negative
% 0.43/0.60  # Parsed axioms                        : 13
% 0.43/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.43/0.60  # Initial clauses                      : 36
% 0.43/0.60  # Removed in clause preprocessing      : 0
% 0.43/0.60  # Initial clauses in saturation        : 36
% 0.43/0.60  # Processed clauses                    : 1660
% 0.43/0.60  # ...of these trivial                  : 73
% 0.43/0.60  # ...subsumed                          : 896
% 0.43/0.60  # ...remaining for further processing  : 691
% 0.43/0.60  # Other redundant clauses eliminated   : 4
% 0.43/0.60  # Clauses deleted for lack of memory   : 0
% 0.43/0.60  # Backward-subsumed                    : 64
% 0.43/0.60  # Backward-rewritten                   : 436
% 0.43/0.60  # Generated clauses                    : 6065
% 0.43/0.60  # ...of the previous two non-trivial   : 5642
% 0.43/0.60  # Contextual simplify-reflections      : 124
% 0.43/0.60  # Paramodulations                      : 6044
% 0.43/0.60  # Factorizations                       : 8
% 0.43/0.60  # Equation resolutions                 : 12
% 0.43/0.60  # Propositional unsat checks           : 0
% 0.43/0.60  #    Propositional check models        : 0
% 0.43/0.60  #    Propositional check unsatisfiable : 0
% 0.43/0.60  #    Propositional clauses             : 0
% 0.43/0.60  #    Propositional clauses after purity: 0
% 0.43/0.60  #    Propositional unsat core size     : 0
% 0.43/0.60  #    Propositional preprocessing time  : 0.000
% 0.43/0.60  #    Propositional encoding time       : 0.000
% 0.43/0.60  #    Propositional solver time         : 0.000
% 0.43/0.60  #    Success case prop preproc time    : 0.000
% 0.43/0.60  #    Success case prop encoding time   : 0.000
% 0.43/0.60  #    Success case prop solver time     : 0.000
% 0.43/0.60  # Current number of processed clauses  : 153
% 0.43/0.60  #    Positive orientable unit clauses  : 15
% 0.43/0.60  #    Positive unorientable unit clauses: 0
% 0.43/0.60  #    Negative unit clauses             : 3
% 0.43/0.60  #    Non-unit-clauses                  : 135
% 0.43/0.60  # Current number of unprocessed clauses: 3709
% 0.43/0.60  # ...number of literals in the above   : 44415
% 0.43/0.60  # Current number of archived formulas  : 0
% 0.43/0.60  # Current number of archived clauses   : 536
% 0.43/0.60  # Clause-clause subsumption calls (NU) : 56189
% 0.43/0.60  # Rec. Clause-clause subsumption calls : 8731
% 0.43/0.60  # Non-unit clause-clause subsumptions  : 1073
% 0.43/0.60  # Unit Clause-clause subsumption calls : 563
% 0.43/0.60  # Rewrite failures with RHS unbound    : 0
% 0.43/0.60  # BW rewrite match attempts            : 14
% 0.43/0.60  # BW rewrite match successes           : 11
% 0.43/0.60  # Condensation attempts                : 0
% 0.43/0.60  # Condensation successes               : 0
% 0.43/0.60  # Termbank termtop insertions          : 212861
% 0.43/0.60  
% 0.43/0.60  # -------------------------------------------------
% 0.43/0.60  # User time                : 0.243 s
% 0.43/0.60  # System time              : 0.007 s
% 0.43/0.60  # Total time               : 0.250 s
% 0.43/0.60  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
