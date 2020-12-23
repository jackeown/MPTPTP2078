%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:11 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 (3092 expanded)
%              Number of clauses        :   77 (1064 expanded)
%              Number of leaves         :   15 ( 775 expanded)
%              Depth                    :   20
%              Number of atoms          :  481 (24093 expanded)
%              Number of equality atoms :  101 (2617 expanded)
%              Maximal formula depth    :   16 (   5 average)
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

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

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

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X35,X36] :
      ( ( v1_funct_1(k4_tmap_1(X35,X36))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X36,X35) )
      & ( v1_funct_2(k4_tmap_1(X35,X36),u1_struct_0(X36),u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X36,X35) )
      & ( m1_subset_1(k4_tmap_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X36,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).

fof(c_0_17,negated_conjecture,(
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
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).

fof(c_0_18,plain,(
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

cnf(c_0_19,plain,
    ( m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | k1_relset_1(X14,X15,X16) = k1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_26,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

fof(c_0_29,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_30,plain,(
    ! [X12,X13] : v1_relat_1(k2_zfmisc_1(X12,X13)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_31,plain,(
    ! [X26,X27,X28] :
      ( ( r1_tarski(k1_relat_1(X26),k1_relat_1(X27))
        | ~ r1_tarski(X26,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( ~ r2_hidden(X28,k1_relat_1(X26))
        | k1_funct_1(X26,X28) = k1_funct_1(X27,X28)
        | ~ r1_tarski(X26,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( r2_hidden(esk2_2(X26,X27),k1_relat_1(X26))
        | ~ r1_tarski(k1_relat_1(X26),k1_relat_1(X27))
        | r1_tarski(X26,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( k1_funct_1(X26,esk2_2(X26,X27)) != k1_funct_1(X27,esk2_2(X26,X27))
        | ~ r1_tarski(k1_relat_1(X26),k1_relat_1(X27))
        | r1_tarski(X26,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_grfunc_1])])])])])).

cnf(c_0_32,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0)) = u1_struct_0(esk4_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_34,plain,
    ( v1_funct_1(k4_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_39,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | r1_tarski(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( k1_relat_1(k4_tmap_1(esk3_0,esk4_0)) = u1_struct_0(esk4_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_27])])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(k4_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_36])])).

cnf(c_0_44,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0) = u1_struct_0(esk4_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_37]),c_0_38])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_46,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,X9)
      | m1_subset_1(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),X1),u1_struct_0(esk4_0))
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(esk5_0) = u1_struct_0(esk4_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_44]),c_0_37])])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_37]),c_0_36])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_53,plain,(
    ! [X32,X33,X34] :
      ( v2_struct_0(X32)
      | ~ l1_pre_topc(X32)
      | v2_struct_0(X33)
      | ~ m1_pre_topc(X33,X32)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | m1_subset_1(X34,u1_struct_0(X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_56,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_57,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_41]),c_0_42]),c_0_43])])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | m1_subset_1(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | k1_funct_1(X1,esk2_2(X1,X2)) != k1_funct_1(X2,esk2_2(X1,X2))
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_62,plain,
    ( k1_funct_1(X2,X1) = k1_funct_1(X3,X1)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r1_tarski(X2,X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(X1,k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(X1))
    | r1_tarski(X1,k4_tmap_1(esk3_0,esk4_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_51]),c_0_49]),c_0_50])])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(X1,esk5_0),k1_relat_1(X1))
    | r1_tarski(X1,esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_51]),c_0_42]),c_0_43])])).

fof(c_0_67,plain,(
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

cnf(c_0_68,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v2_struct_0(X1)
    | m1_subset_1(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(X1))
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_69,plain,
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
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(esk5_0))
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_49]),c_0_50])])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),k1_relat_1(k4_tmap_1(esk3_0,esk4_0)))
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_42]),c_0_43])])).

cnf(c_0_72,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_funct_1(k4_tmap_1(X1,X2),X3) = X3
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | m1_subset_1(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_20]),c_0_22])]),c_0_23])).

cnf(c_0_75,negated_conjecture,
    ( X1 = k1_funct_1(esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_76,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) != k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))
    | ~ r1_tarski(k1_relat_1(esk5_0),k1_relat_1(k4_tmap_1(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_42]),c_0_49]),c_0_43]),c_0_50]),c_0_51])])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) != k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_71]),c_0_49]),c_0_42]),c_0_50]),c_0_43]),c_0_51])])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(u1_struct_0(esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_51]),c_0_49]),c_0_50])])).

cnf(c_0_79,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,X1),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | u1_struct_0(esk3_0) = k1_xboole_0
    | v2_struct_0(X1)
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_80,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | ~ m1_subset_1(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_55])).

cnf(c_0_81,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) != k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_41]),c_0_64])).

cnf(c_0_82,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(esk5_0,X1),u1_struct_0(esk4_0))
    | r1_tarski(esk5_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_83,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) != k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_41]),c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_55]),c_0_20])]),c_0_60])).

cnf(c_0_85,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_74])).

cnf(c_0_86,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | k1_funct_1(X1,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) != k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(k4_tmap_1(esk3_0,esk4_0)))
    | ~ r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_62]),c_0_42]),c_0_43])])).

cnf(c_0_87,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_41]),c_0_42]),c_0_43]),c_0_51])])).

cnf(c_0_88,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_89,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | k1_funct_1(X1,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) != k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_41]),c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( k4_tmap_1(esk3_0,esk4_0) = esk5_0
    | u1_struct_0(esk3_0) = k1_xboole_0
    | ~ r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_92,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_89]),c_0_49]),c_0_50])])).

fof(c_0_93,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( ~ r2_funct_2(X20,X21,X22,X23)
        | ~ m1_subset_1(X24,X20)
        | k1_funct_1(X22,X24) = k1_funct_1(X23,X24)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( m1_subset_1(esk1_4(X20,X21,X22,X23),X20)
        | r2_funct_2(X20,X21,X22,X23)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( k1_funct_1(X22,esk1_4(X20,X21,X22,X23)) != k1_funct_1(X23,esk1_4(X20,X21,X22,X23))
        | r2_funct_2(X20,X21,X22,X23)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_95,negated_conjecture,
    ( k4_tmap_1(esk3_0,esk4_0) = esk5_0
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,plain,
    ( r2_funct_2(X2,X3,X1,X4)
    | k1_funct_1(X1,esk1_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk1_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

fof(c_0_97,plain,(
    ! [X31] :
      ( v2_struct_0(X31)
      | ~ l1_struct_0(X31)
      | ~ v1_xboole_0(u1_struct_0(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_98,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_96])).

cnf(c_0_100,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_49]),c_0_38]),c_0_37])])).

cnf(c_0_102,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_103,plain,(
    ! [X30] :
      ( ~ l1_pre_topc(X30)
      | l1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_104,negated_conjecture,
    ( ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102])]),c_0_23])).

cnf(c_0_105,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:48:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.21/0.49  # and selection function PSelectComplexExceptRRHorn.
% 0.21/0.49  #
% 0.21/0.49  # Preprocessing time       : 0.029 s
% 0.21/0.49  # Presaturation interreduction done
% 0.21/0.49  
% 0.21/0.49  # Proof found!
% 0.21/0.49  # SZS status Theorem
% 0.21/0.49  # SZS output start CNFRefutation
% 0.21/0.49  fof(t96_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 0.21/0.49  fof(dt_k4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k4_tmap_1(X1,X2))&v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 0.21/0.49  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.49  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.49  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.49  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.49  fof(t8_grfunc_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,X2)<=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_grfunc_1)).
% 0.21/0.49  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.49  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.21/0.49  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.21/0.49  fof(t95_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,u1_struct_0(X2))=>k1_funct_1(k4_tmap_1(X1,X2),X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 0.21/0.49  fof(d9_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_2)).
% 0.21/0.49  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.21/0.49  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.21/0.49  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.49  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t96_tmap_1])).
% 0.21/0.49  fof(c_0_16, plain, ![X35, X36]:(((v1_funct_1(k4_tmap_1(X35,X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35)))&(v1_funct_2(k4_tmap_1(X35,X36),u1_struct_0(X36),u1_struct_0(X35))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35))))&(m1_subset_1(k4_tmap_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).
% 0.21/0.49  fof(c_0_17, negated_conjecture, ![X43]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))))&((~m1_subset_1(X43,u1_struct_0(esk3_0))|(~r2_hidden(X43,u1_struct_0(esk4_0))|X43=k1_funct_1(esk5_0,X43)))&~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).
% 0.21/0.49  fof(c_0_18, plain, ![X17, X18, X19]:((((~v1_funct_2(X19,X17,X18)|X17=k1_relset_1(X17,X18,X19)|X18=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(X17!=k1_relset_1(X17,X18,X19)|v1_funct_2(X19,X17,X18)|X18=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&((~v1_funct_2(X19,X17,X18)|X17=k1_relset_1(X17,X18,X19)|X17!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(X17!=k1_relset_1(X17,X18,X19)|v1_funct_2(X19,X17,X18)|X17!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))))&((~v1_funct_2(X19,X17,X18)|X19=k1_xboole_0|X17=k1_xboole_0|X18!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(X19!=k1_xboole_0|v1_funct_2(X19,X17,X18)|X17=k1_xboole_0|X18!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.49  cnf(c_0_19, plain, (m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_20, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.49  cnf(c_0_21, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.49  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.49  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.49  cnf(c_0_24, plain, (v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  fof(c_0_25, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|k1_relset_1(X14,X15,X16)=k1_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.49  cnf(c_0_26, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.49  cnf(c_0_27, negated_conjecture, (m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.21/0.49  cnf(c_0_28, negated_conjecture, (v1_funct_2(k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.21/0.49  fof(c_0_29, plain, ![X10, X11]:(~v1_relat_1(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_relat_1(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.49  fof(c_0_30, plain, ![X12, X13]:v1_relat_1(k2_zfmisc_1(X12,X13)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.49  fof(c_0_31, plain, ![X26, X27, X28]:(((r1_tarski(k1_relat_1(X26),k1_relat_1(X27))|~r1_tarski(X26,X27)|(~v1_relat_1(X27)|~v1_funct_1(X27))|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(~r2_hidden(X28,k1_relat_1(X26))|k1_funct_1(X26,X28)=k1_funct_1(X27,X28)|~r1_tarski(X26,X27)|(~v1_relat_1(X27)|~v1_funct_1(X27))|(~v1_relat_1(X26)|~v1_funct_1(X26))))&((r2_hidden(esk2_2(X26,X27),k1_relat_1(X26))|~r1_tarski(k1_relat_1(X26),k1_relat_1(X27))|r1_tarski(X26,X27)|(~v1_relat_1(X27)|~v1_funct_1(X27))|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(k1_funct_1(X26,esk2_2(X26,X27))!=k1_funct_1(X27,esk2_2(X26,X27))|~r1_tarski(k1_relat_1(X26),k1_relat_1(X27))|r1_tarski(X26,X27)|(~v1_relat_1(X27)|~v1_funct_1(X27))|(~v1_relat_1(X26)|~v1_funct_1(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_grfunc_1])])])])])).
% 0.21/0.49  cnf(c_0_32, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.49  cnf(c_0_33, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0))=u1_struct_0(esk4_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.21/0.49  cnf(c_0_34, plain, (v1_funct_1(k4_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_35, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.49  cnf(c_0_36, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.49  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.49  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.49  fof(c_0_39, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.49  cnf(c_0_40, plain, (r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))|r1_tarski(X1,X2)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.49  cnf(c_0_41, negated_conjecture, (k1_relat_1(k4_tmap_1(esk3_0,esk4_0))=u1_struct_0(esk4_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_27])])).
% 0.21/0.49  cnf(c_0_42, negated_conjecture, (v1_funct_1(k4_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.21/0.49  cnf(c_0_43, negated_conjecture, (v1_relat_1(k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_27]), c_0_36])])).
% 0.21/0.49  cnf(c_0_44, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0)=u1_struct_0(esk4_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_37]), c_0_38])])).
% 0.21/0.49  cnf(c_0_45, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.49  fof(c_0_46, plain, ![X8, X9]:(~r2_hidden(X8,X9)|m1_subset_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.21/0.49  cnf(c_0_47, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),X1),u1_struct_0(esk4_0))|r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43])])).
% 0.21/0.49  cnf(c_0_48, negated_conjecture, (k1_relat_1(esk5_0)=u1_struct_0(esk4_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_44]), c_0_37])])).
% 0.21/0.49  cnf(c_0_49, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.49  cnf(c_0_50, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_37]), c_0_36])])).
% 0.21/0.49  cnf(c_0_51, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_45])).
% 0.21/0.49  cnf(c_0_52, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.49  fof(c_0_53, plain, ![X32, X33, X34]:(v2_struct_0(X32)|~l1_pre_topc(X32)|(v2_struct_0(X33)|~m1_pre_topc(X33,X32)|(~m1_subset_1(X34,u1_struct_0(X33))|m1_subset_1(X34,u1_struct_0(X32))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.21/0.49  cnf(c_0_54, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.49  cnf(c_0_55, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), c_0_51])])).
% 0.21/0.49  cnf(c_0_56, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_48]), c_0_49]), c_0_50])])).
% 0.21/0.49  cnf(c_0_57, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X1,k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_41]), c_0_42]), c_0_43])])).
% 0.21/0.49  cnf(c_0_58, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.49  cnf(c_0_59, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|m1_subset_1(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.49  cnf(c_0_60, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.49  cnf(c_0_61, plain, (r1_tarski(X1,X2)|k1_funct_1(X1,esk2_2(X1,X2))!=k1_funct_1(X2,esk2_2(X1,X2))|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.49  cnf(c_0_62, plain, (k1_funct_1(X2,X1)=k1_funct_1(X3,X1)|~r2_hidden(X1,k1_relat_1(X2))|~r1_tarski(X2,X3)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.49  cnf(c_0_63, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(X1,k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(X1))|r1_tarski(X1,k4_tmap_1(esk3_0,esk4_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43])])).
% 0.21/0.49  cnf(c_0_64, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k1_relat_1(esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_51]), c_0_49]), c_0_50])])).
% 0.21/0.49  cnf(c_0_65, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(X1,esk5_0),k1_relat_1(X1))|r1_tarski(X1,esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_48]), c_0_49]), c_0_50])])).
% 0.21/0.49  cnf(c_0_66, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k1_relat_1(k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_51]), c_0_42]), c_0_43])])).
% 0.21/0.49  fof(c_0_67, plain, ![X37, X38, X39]:(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|(v2_struct_0(X38)|~m1_pre_topc(X38,X37)|(~m1_subset_1(X39,u1_struct_0(X37))|(~r2_hidden(X39,u1_struct_0(X38))|k1_funct_1(k4_tmap_1(X37,X38),X39)=X39)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).
% 0.21/0.49  cnf(c_0_68, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v2_struct_0(X1)|m1_subset_1(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(X1))|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.21/0.49  cnf(c_0_69, plain, (r1_tarski(X1,X2)|k1_funct_1(X3,esk2_2(X1,X2))!=k1_funct_1(X2,esk2_2(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X3)|~r2_hidden(esk2_2(X1,X2),k1_relat_1(X3))|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.21/0.49  cnf(c_0_70, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(esk5_0))|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_49]), c_0_50])])).
% 0.21/0.49  cnf(c_0_71, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),k1_relat_1(k4_tmap_1(esk3_0,esk4_0)))|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_42]), c_0_43])])).
% 0.21/0.49  cnf(c_0_72, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_48]), c_0_49]), c_0_50])])).
% 0.21/0.49  cnf(c_0_73, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_funct_1(k4_tmap_1(X1,X2),X3)=X3|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.21/0.49  cnf(c_0_74, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|m1_subset_1(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_20]), c_0_22])]), c_0_23])).
% 0.21/0.49  cnf(c_0_75, negated_conjecture, (X1=k1_funct_1(esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.49  cnf(c_0_76, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))|k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))!=k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))|~r1_tarski(k1_relat_1(esk5_0),k1_relat_1(k4_tmap_1(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_42]), c_0_49]), c_0_43]), c_0_50]), c_0_51])])).
% 0.21/0.49  cnf(c_0_77, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)|k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))!=k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))|~r1_tarski(k1_relat_1(k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_71]), c_0_49]), c_0_42]), c_0_50]), c_0_43]), c_0_51])])).
% 0.21/0.49  cnf(c_0_78, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(u1_struct_0(esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_51]), c_0_49]), c_0_50])])).
% 0.21/0.49  cnf(c_0_79, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,X1),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)|u1_struct_0(esk3_0)=k1_xboole_0|v2_struct_0(X1)|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)|~m1_pre_topc(X1,esk3_0)|~r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_21]), c_0_22])]), c_0_23])).
% 0.21/0.49  cnf(c_0_80, negated_conjecture, (k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)|u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)|~m1_subset_1(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_75, c_0_55])).
% 0.21/0.49  cnf(c_0_81, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))|k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))!=k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_41]), c_0_64])).
% 0.21/0.49  cnf(c_0_82, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(esk5_0,X1),u1_struct_0(esk4_0))|r1_tarski(esk5_0,X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_48]), c_0_49]), c_0_50])])).
% 0.21/0.49  cnf(c_0_83, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)|k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))!=k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_41]), c_0_78])).
% 0.21/0.49  cnf(c_0_84, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)|u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_55]), c_0_20])]), c_0_60])).
% 0.21/0.49  cnf(c_0_85, negated_conjecture, (k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)|u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_80, c_0_74])).
% 0.21/0.49  cnf(c_0_86, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))|k1_funct_1(X1,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))!=k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(k4_tmap_1(esk3_0,esk4_0)))|~r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_62]), c_0_42]), c_0_43])])).
% 0.21/0.49  cnf(c_0_87, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_41]), c_0_42]), c_0_43]), c_0_51])])).
% 0.21/0.49  cnf(c_0_88, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.49  cnf(c_0_89, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 0.21/0.49  cnf(c_0_90, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))|k1_funct_1(X1,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))!=k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k4_tmap_1(esk3_0,esk4_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_41]), c_0_87])).
% 0.21/0.49  cnf(c_0_91, negated_conjecture, (k4_tmap_1(esk3_0,esk4_0)=esk5_0|u1_struct_0(esk3_0)=k1_xboole_0|~r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.21/0.49  cnf(c_0_92, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_89]), c_0_49]), c_0_50])])).
% 0.21/0.49  fof(c_0_93, plain, ![X20, X21, X22, X23, X24]:((~r2_funct_2(X20,X21,X22,X23)|(~m1_subset_1(X24,X20)|k1_funct_1(X22,X24)=k1_funct_1(X23,X24))|(~v1_funct_1(X23)|~v1_funct_2(X23,X20,X21)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))|(~v1_funct_1(X22)|~v1_funct_2(X22,X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))&((m1_subset_1(esk1_4(X20,X21,X22,X23),X20)|r2_funct_2(X20,X21,X22,X23)|(~v1_funct_1(X23)|~v1_funct_2(X23,X20,X21)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))|(~v1_funct_1(X22)|~v1_funct_2(X22,X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))&(k1_funct_1(X22,esk1_4(X20,X21,X22,X23))!=k1_funct_1(X23,esk1_4(X20,X21,X22,X23))|r2_funct_2(X20,X21,X22,X23)|(~v1_funct_1(X23)|~v1_funct_2(X23,X20,X21)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))|(~v1_funct_1(X22)|~v1_funct_2(X22,X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).
% 0.21/0.49  cnf(c_0_94, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.49  cnf(c_0_95, negated_conjecture, (k4_tmap_1(esk3_0,esk4_0)=esk5_0|u1_struct_0(esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.21/0.49  cnf(c_0_96, plain, (r2_funct_2(X2,X3,X1,X4)|k1_funct_1(X1,esk1_4(X2,X3,X1,X4))!=k1_funct_1(X4,esk1_4(X2,X3,X1,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.21/0.49  fof(c_0_97, plain, ![X31]:(v2_struct_0(X31)|~l1_struct_0(X31)|~v1_xboole_0(u1_struct_0(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.21/0.49  cnf(c_0_98, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.21/0.49  cnf(c_0_99, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_96])).
% 0.21/0.49  cnf(c_0_100, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.21/0.49  cnf(c_0_101, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_49]), c_0_38]), c_0_37])])).
% 0.21/0.49  cnf(c_0_102, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.21/0.49  fof(c_0_103, plain, ![X30]:(~l1_pre_topc(X30)|l1_struct_0(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.49  cnf(c_0_104, negated_conjecture, (~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102])]), c_0_23])).
% 0.21/0.49  cnf(c_0_105, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.21/0.49  cnf(c_0_106, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_22])]), ['proof']).
% 0.21/0.49  # SZS output end CNFRefutation
% 0.21/0.49  # Proof object total steps             : 107
% 0.21/0.49  # Proof object clause steps            : 77
% 0.21/0.49  # Proof object formula steps           : 30
% 0.21/0.49  # Proof object conjectures             : 57
% 0.21/0.49  # Proof object clause conjectures      : 54
% 0.21/0.49  # Proof object formula conjectures     : 3
% 0.21/0.49  # Proof object initial clauses used    : 30
% 0.21/0.49  # Proof object initial formulas used   : 15
% 0.21/0.49  # Proof object generating inferences   : 46
% 0.21/0.49  # Proof object simplifying inferences  : 111
% 0.21/0.49  # Training examples: 0 positive, 0 negative
% 0.21/0.49  # Parsed axioms                        : 15
% 0.21/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.49  # Initial clauses                      : 38
% 0.21/0.49  # Removed in clause preprocessing      : 0
% 0.21/0.49  # Initial clauses in saturation        : 38
% 0.21/0.49  # Processed clauses                    : 693
% 0.21/0.49  # ...of these trivial                  : 3
% 0.21/0.49  # ...subsumed                          : 336
% 0.21/0.49  # ...remaining for further processing  : 354
% 0.21/0.49  # Other redundant clauses eliminated   : 4
% 0.21/0.49  # Clauses deleted for lack of memory   : 0
% 0.21/0.49  # Backward-subsumed                    : 60
% 0.21/0.49  # Backward-rewritten                   : 104
% 0.21/0.49  # Generated clauses                    : 2075
% 0.21/0.49  # ...of the previous two non-trivial   : 1911
% 0.21/0.49  # Contextual simplify-reflections      : 28
% 0.21/0.49  # Paramodulations                      : 2053
% 0.21/0.49  # Factorizations                       : 10
% 0.21/0.49  # Equation resolutions                 : 12
% 0.21/0.49  # Propositional unsat checks           : 0
% 0.21/0.49  #    Propositional check models        : 0
% 0.21/0.49  #    Propositional check unsatisfiable : 0
% 0.21/0.49  #    Propositional clauses             : 0
% 0.21/0.49  #    Propositional clauses after purity: 0
% 0.21/0.49  #    Propositional unsat core size     : 0
% 0.21/0.49  #    Propositional preprocessing time  : 0.000
% 0.21/0.49  #    Propositional encoding time       : 0.000
% 0.21/0.49  #    Propositional solver time         : 0.000
% 0.21/0.49  #    Success case prop preproc time    : 0.000
% 0.21/0.49  #    Success case prop encoding time   : 0.000
% 0.21/0.49  #    Success case prop solver time     : 0.000
% 0.21/0.49  # Current number of processed clauses  : 151
% 0.21/0.49  #    Positive orientable unit clauses  : 11
% 0.21/0.49  #    Positive unorientable unit clauses: 0
% 0.21/0.49  #    Negative unit clauses             : 3
% 0.21/0.49  #    Non-unit-clauses                  : 137
% 0.21/0.49  # Current number of unprocessed clauses: 1282
% 0.21/0.49  # ...number of literals in the above   : 15640
% 0.21/0.49  # Current number of archived formulas  : 0
% 0.21/0.49  # Current number of archived clauses   : 201
% 0.21/0.49  # Clause-clause subsumption calls (NU) : 27218
% 0.21/0.49  # Rec. Clause-clause subsumption calls : 2956
% 0.21/0.49  # Non-unit clause-clause subsumptions  : 416
% 0.21/0.49  # Unit Clause-clause subsumption calls : 94
% 0.21/0.49  # Rewrite failures with RHS unbound    : 0
% 0.21/0.49  # BW rewrite match attempts            : 2
% 0.21/0.49  # BW rewrite match successes           : 1
% 0.21/0.49  # Condensation attempts                : 0
% 0.21/0.49  # Condensation successes               : 0
% 0.21/0.49  # Termbank termtop insertions          : 86691
% 0.21/0.49  
% 0.21/0.49  # -------------------------------------------------
% 0.21/0.49  # User time                : 0.140 s
% 0.21/0.49  # System time              : 0.008 s
% 0.21/0.49  # Total time               : 0.148 s
% 0.21/0.49  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
