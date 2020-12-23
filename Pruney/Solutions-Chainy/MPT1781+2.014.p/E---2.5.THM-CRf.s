%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:11 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  101 (2847 expanded)
%              Number of clauses        :   73 ( 984 expanded)
%              Number of leaves         :   14 ( 703 expanded)
%              Depth                    :   20
%              Number of atoms          :  459 (22852 expanded)
%              Number of equality atoms :   97 (2552 expanded)
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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X34,X35] :
      ( ( v1_funct_1(k4_tmap_1(X34,X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_pre_topc(X35,X34) )
      & ( v1_funct_2(k4_tmap_1(X34,X35),u1_struct_0(X35),u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_pre_topc(X35,X34) )
      & ( m1_subset_1(k4_tmap_1(X34,X35),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X34))))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_pre_topc(X35,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).

fof(c_0_16,negated_conjecture,(
    ! [X42] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
      & ( ~ m1_subset_1(X42,u1_struct_0(esk3_0))
        | ~ r2_hidden(X42,u1_struct_0(esk4_0))
        | X42 = k1_funct_1(esk5_0,X42) )
      & ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).

fof(c_0_17,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v1_funct_2(X18,X16,X17)
        | X16 = k1_relset_1(X16,X17,X18)
        | X17 = k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( X16 != k1_relset_1(X16,X17,X18)
        | v1_funct_2(X18,X16,X17)
        | X17 = k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( ~ v1_funct_2(X18,X16,X17)
        | X16 = k1_relset_1(X16,X17,X18)
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( X16 != k1_relset_1(X16,X17,X18)
        | v1_funct_2(X18,X16,X17)
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( ~ v1_funct_2(X18,X16,X17)
        | X18 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( X18 != k1_xboole_0
        | v1_funct_2(X18,X16,X17)
        | X16 = k1_xboole_0
        | X17 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k1_relset_1(X13,X14,X15) = k1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_25,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

fof(c_0_28,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | v1_relat_1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_29,plain,(
    ! [X25,X26,X27] :
      ( ( r1_tarski(k1_relat_1(X25),k1_relat_1(X26))
        | ~ r1_tarski(X25,X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( ~ r2_hidden(X27,k1_relat_1(X25))
        | k1_funct_1(X25,X27) = k1_funct_1(X26,X27)
        | ~ r1_tarski(X25,X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( r2_hidden(esk2_2(X25,X26),k1_relat_1(X25))
        | ~ r1_tarski(k1_relat_1(X25),k1_relat_1(X26))
        | r1_tarski(X25,X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( k1_funct_1(X25,esk2_2(X25,X26)) != k1_funct_1(X26,esk2_2(X25,X26))
        | ~ r1_tarski(k1_relat_1(X25),k1_relat_1(X26))
        | r1_tarski(X25,X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_grfunc_1])])])])])).

cnf(c_0_30,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0)) = u1_struct_0(esk4_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_32,plain,
    ( v1_funct_1(k4_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

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

cnf(c_0_37,plain,
    ( r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | r1_tarski(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(k4_tmap_1(esk3_0,esk4_0)) = u1_struct_0(esk4_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_26])])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(k4_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(k4_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0) = u1_struct_0(esk4_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_34]),c_0_35])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_43,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,X9)
      | m1_subset_1(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(X1,k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(X1))
    | r1_tarski(X1,k4_tmap_1(esk3_0,esk4_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(esk5_0) = u1_struct_0(esk4_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_41]),c_0_34])])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_50,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ l1_pre_topc(X31)
      | v2_struct_0(X32)
      | ~ m1_pre_topc(X32,X31)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | m1_subset_1(X33,u1_struct_0(X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48])])).

cnf(c_0_53,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | m1_subset_1(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | k1_funct_1(X1,esk2_2(X1,X2)) != k1_funct_1(X2,esk2_2(X1,X2))
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_58,plain,
    ( k1_funct_1(X2,X1) = k1_funct_1(X3,X1)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r1_tarski(X2,X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_48]),c_0_46]),c_0_47])])).

fof(c_0_60,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | v2_struct_0(X37)
      | ~ m1_pre_topc(X37,X36)
      | ~ m1_subset_1(X38,u1_struct_0(X36))
      | ~ r2_hidden(X38,u1_struct_0(X37))
      | k1_funct_1(k4_tmap_1(X36,X37),X38) = X38 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v2_struct_0(X1)
    | m1_subset_1(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X1))
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_63,plain,
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
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(esk5_0))
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_59]),c_0_46]),c_0_47])])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_funct_1(k4_tmap_1(X1,X2),X3) = X3
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | m1_subset_1(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk3_0))
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_19]),c_0_21])]),c_0_22])).

cnf(c_0_67,negated_conjecture,
    ( X1 = k1_funct_1(esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_68,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(X1,esk5_0),k1_relat_1(X1))
    | r1_tarski(X1,esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_48]),c_0_39]),c_0_40])])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) != k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))
    | ~ r1_tarski(k1_relat_1(esk5_0),k1_relat_1(k4_tmap_1(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_39]),c_0_46]),c_0_40]),c_0_47]),c_0_48])])).

cnf(c_0_71,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,X1),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | u1_struct_0(esk3_0) = k1_xboole_0
    | v2_struct_0(X1)
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_72,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_52])).

cnf(c_0_73,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),k1_relat_1(k4_tmap_1(esk3_0,esk4_0)))
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_39]),c_0_40])])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_75,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = k1_funct_1(X2,X1)
    | u1_struct_0(esk3_0) = k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r1_tarski(esk5_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_76,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_38]),c_0_39]),c_0_40]),c_0_48])])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) != k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_38]),c_0_59])).

cnf(c_0_78,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_52]),c_0_19])]),c_0_56])).

cnf(c_0_79,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_66])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) != k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_73]),c_0_46]),c_0_39]),c_0_47]),c_0_40]),c_0_48])])).

cnf(c_0_81,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(u1_struct_0(esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_48]),c_0_46]),c_0_47])])).

cnf(c_0_82,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) = k1_funct_1(X1,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))
    | u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) != k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_38]),c_0_81])).

cnf(c_0_85,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_86,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_39]),c_0_40])]),c_0_84])).

fof(c_0_87,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( ~ r2_funct_2(X19,X20,X21,X22)
        | ~ m1_subset_1(X23,X19)
        | k1_funct_1(X21,X23) = k1_funct_1(X22,X23)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( m1_subset_1(esk1_4(X19,X20,X21,X22),X19)
        | r2_funct_2(X19,X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( k1_funct_1(X21,esk1_4(X19,X20,X21,X22)) != k1_funct_1(X22,esk1_4(X19,X20,X21,X22))
        | r2_funct_2(X19,X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).

cnf(c_0_88,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_89,negated_conjecture,
    ( k4_tmap_1(esk3_0,esk4_0) = esk5_0
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_83])).

cnf(c_0_90,plain,
    ( r2_funct_2(X2,X3,X1,X4)
    | k1_funct_1(X1,esk1_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk1_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

fof(c_0_91,plain,(
    ! [X30] :
      ( v2_struct_0(X30)
      | ~ l1_struct_0(X30)
      | ~ v1_xboole_0(u1_struct_0(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_92,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_93,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_90])).

cnf(c_0_94,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_46]),c_0_35]),c_0_34])])).

cnf(c_0_96,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_97,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_98,negated_conjecture,
    ( ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])]),c_0_22])).

cnf(c_0_99,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:35:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.18/0.44  # and selection function PSelectComplexExceptRRHorn.
% 0.18/0.44  #
% 0.18/0.44  # Preprocessing time       : 0.029 s
% 0.18/0.44  # Presaturation interreduction done
% 0.18/0.44  
% 0.18/0.44  # Proof found!
% 0.18/0.44  # SZS status Theorem
% 0.18/0.44  # SZS output start CNFRefutation
% 0.18/0.44  fof(t96_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 0.18/0.44  fof(dt_k4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k4_tmap_1(X1,X2))&v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 0.18/0.44  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.18/0.44  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.18/0.44  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.18/0.44  fof(t8_grfunc_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,X2)<=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_grfunc_1)).
% 0.18/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.44  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.18/0.44  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.18/0.44  fof(t95_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,u1_struct_0(X2))=>k1_funct_1(k4_tmap_1(X1,X2),X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 0.18/0.44  fof(d9_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_2)).
% 0.18/0.44  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.18/0.44  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.44  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.18/0.44  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t96_tmap_1])).
% 0.18/0.44  fof(c_0_15, plain, ![X34, X35]:(((v1_funct_1(k4_tmap_1(X34,X35))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|~m1_pre_topc(X35,X34)))&(v1_funct_2(k4_tmap_1(X34,X35),u1_struct_0(X35),u1_struct_0(X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|~m1_pre_topc(X35,X34))))&(m1_subset_1(k4_tmap_1(X34,X35),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X34))))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|~m1_pre_topc(X35,X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).
% 0.18/0.44  fof(c_0_16, negated_conjecture, ![X42]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))))&((~m1_subset_1(X42,u1_struct_0(esk3_0))|(~r2_hidden(X42,u1_struct_0(esk4_0))|X42=k1_funct_1(esk5_0,X42)))&~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).
% 0.18/0.44  fof(c_0_17, plain, ![X16, X17, X18]:((((~v1_funct_2(X18,X16,X17)|X16=k1_relset_1(X16,X17,X18)|X17=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(X16!=k1_relset_1(X16,X17,X18)|v1_funct_2(X18,X16,X17)|X17=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))&((~v1_funct_2(X18,X16,X17)|X16=k1_relset_1(X16,X17,X18)|X16!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(X16!=k1_relset_1(X16,X17,X18)|v1_funct_2(X18,X16,X17)|X16!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))&((~v1_funct_2(X18,X16,X17)|X18=k1_xboole_0|X16=k1_xboole_0|X17!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(X18!=k1_xboole_0|v1_funct_2(X18,X16,X17)|X16=k1_xboole_0|X17!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.18/0.44  cnf(c_0_18, plain, (m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.44  cnf(c_0_19, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_20, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_23, plain, (v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.44  fof(c_0_24, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|k1_relset_1(X13,X14,X15)=k1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.18/0.44  cnf(c_0_25, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.44  cnf(c_0_26, negated_conjecture, (m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.18/0.44  cnf(c_0_27, negated_conjecture, (v1_funct_2(k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.18/0.44  fof(c_0_28, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|v1_relat_1(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.18/0.44  fof(c_0_29, plain, ![X25, X26, X27]:(((r1_tarski(k1_relat_1(X25),k1_relat_1(X26))|~r1_tarski(X25,X26)|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(~r2_hidden(X27,k1_relat_1(X25))|k1_funct_1(X25,X27)=k1_funct_1(X26,X27)|~r1_tarski(X25,X26)|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25))))&((r2_hidden(esk2_2(X25,X26),k1_relat_1(X25))|~r1_tarski(k1_relat_1(X25),k1_relat_1(X26))|r1_tarski(X25,X26)|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(k1_funct_1(X25,esk2_2(X25,X26))!=k1_funct_1(X26,esk2_2(X25,X26))|~r1_tarski(k1_relat_1(X25),k1_relat_1(X26))|r1_tarski(X25,X26)|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_grfunc_1])])])])])).
% 0.18/0.44  cnf(c_0_30, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.44  cnf(c_0_31, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0))=u1_struct_0(esk4_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.18/0.44  cnf(c_0_32, plain, (v1_funct_1(k4_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.44  cnf(c_0_33, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.44  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  fof(c_0_36, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.44  cnf(c_0_37, plain, (r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))|r1_tarski(X1,X2)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.44  cnf(c_0_38, negated_conjecture, (k1_relat_1(k4_tmap_1(esk3_0,esk4_0))=u1_struct_0(esk4_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_26])])).
% 0.18/0.44  cnf(c_0_39, negated_conjecture, (v1_funct_1(k4_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.18/0.44  cnf(c_0_40, negated_conjecture, (v1_relat_1(k4_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_33, c_0_26])).
% 0.18/0.44  cnf(c_0_41, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0)=u1_struct_0(esk4_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_34]), c_0_35])])).
% 0.18/0.44  cnf(c_0_42, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.44  fof(c_0_43, plain, ![X8, X9]:(~r2_hidden(X8,X9)|m1_subset_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.18/0.44  cnf(c_0_44, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(X1,k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(X1))|r1_tarski(X1,k4_tmap_1(esk3_0,esk4_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 0.18/0.44  cnf(c_0_45, negated_conjecture, (k1_relat_1(esk5_0)=u1_struct_0(esk4_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_41]), c_0_34])])).
% 0.18/0.44  cnf(c_0_46, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.44  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_42])).
% 0.18/0.44  cnf(c_0_49, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.44  fof(c_0_50, plain, ![X31, X32, X33]:(v2_struct_0(X31)|~l1_pre_topc(X31)|(v2_struct_0(X32)|~m1_pre_topc(X32,X31)|(~m1_subset_1(X33,u1_struct_0(X32))|m1_subset_1(X33,u1_struct_0(X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.18/0.44  cnf(c_0_51, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.44  cnf(c_0_52, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_48])])).
% 0.18/0.44  cnf(c_0_53, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_45]), c_0_46]), c_0_47])])).
% 0.18/0.44  cnf(c_0_54, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.18/0.44  cnf(c_0_55, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|m1_subset_1(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.18/0.44  cnf(c_0_56, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_57, plain, (r1_tarski(X1,X2)|k1_funct_1(X1,esk2_2(X1,X2))!=k1_funct_1(X2,esk2_2(X1,X2))|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.44  cnf(c_0_58, plain, (k1_funct_1(X2,X1)=k1_funct_1(X3,X1)|~r2_hidden(X1,k1_relat_1(X2))|~r1_tarski(X2,X3)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.44  cnf(c_0_59, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k1_relat_1(esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_48]), c_0_46]), c_0_47])])).
% 0.18/0.44  fof(c_0_60, plain, ![X36, X37, X38]:(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|(v2_struct_0(X37)|~m1_pre_topc(X37,X36)|(~m1_subset_1(X38,u1_struct_0(X36))|(~r2_hidden(X38,u1_struct_0(X37))|k1_funct_1(k4_tmap_1(X36,X37),X38)=X38)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).
% 0.18/0.44  cnf(c_0_61, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v2_struct_0(X1)|m1_subset_1(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X1))|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.18/0.44  cnf(c_0_62, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X1,k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_38]), c_0_39]), c_0_40])])).
% 0.18/0.44  cnf(c_0_63, plain, (r1_tarski(X1,X2)|k1_funct_1(X3,esk2_2(X1,X2))!=k1_funct_1(X2,esk2_2(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X3)|~r2_hidden(esk2_2(X1,X2),k1_relat_1(X3))|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.18/0.44  cnf(c_0_64, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(esk5_0))|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_59]), c_0_46]), c_0_47])])).
% 0.18/0.44  cnf(c_0_65, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_funct_1(k4_tmap_1(X1,X2),X3)=X3|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.18/0.44  cnf(c_0_66, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|m1_subset_1(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk3_0))|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_19]), c_0_21])]), c_0_22])).
% 0.18/0.44  cnf(c_0_67, negated_conjecture, (X1=k1_funct_1(esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_68, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(X1,esk5_0),k1_relat_1(X1))|r1_tarski(X1,esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_45]), c_0_46]), c_0_47])])).
% 0.18/0.44  cnf(c_0_69, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k1_relat_1(k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_48]), c_0_39]), c_0_40])])).
% 0.18/0.44  cnf(c_0_70, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))|k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))!=k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))|~r1_tarski(k1_relat_1(esk5_0),k1_relat_1(k4_tmap_1(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_39]), c_0_46]), c_0_40]), c_0_47]), c_0_48])])).
% 0.18/0.44  cnf(c_0_71, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,X1),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))|u1_struct_0(esk3_0)=k1_xboole_0|v2_struct_0(X1)|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(X1,esk3_0)|~r2_hidden(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_20]), c_0_21])]), c_0_22])).
% 0.18/0.44  cnf(c_0_72, negated_conjecture, (k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))|u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))|~m1_subset_1(esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_67, c_0_52])).
% 0.18/0.44  cnf(c_0_73, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),k1_relat_1(k4_tmap_1(esk3_0,esk4_0)))|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_39]), c_0_40])])).
% 0.18/0.44  cnf(c_0_74, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(u1_struct_0(esk4_0),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_45]), c_0_46]), c_0_47])])).
% 0.18/0.44  cnf(c_0_75, negated_conjecture, (k1_funct_1(esk5_0,X1)=k1_funct_1(X2,X1)|u1_struct_0(esk3_0)=k1_xboole_0|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,u1_struct_0(esk4_0))|~r1_tarski(esk5_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_45]), c_0_46]), c_0_47])])).
% 0.18/0.44  cnf(c_0_76, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_38]), c_0_39]), c_0_40]), c_0_48])])).
% 0.18/0.44  cnf(c_0_77, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))|k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))!=k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_38]), c_0_59])).
% 0.18/0.44  cnf(c_0_78, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))|u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_52]), c_0_19])]), c_0_56])).
% 0.18/0.44  cnf(c_0_79, negated_conjecture, (k1_funct_1(esk5_0,esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_2(esk5_0,k4_tmap_1(esk3_0,esk4_0))|u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_72, c_0_66])).
% 0.18/0.44  cnf(c_0_80, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)|k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))!=k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))|~r1_tarski(k1_relat_1(k4_tmap_1(esk3_0,esk4_0)),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_73]), c_0_46]), c_0_39]), c_0_47]), c_0_40]), c_0_48])])).
% 0.18/0.44  cnf(c_0_81, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(u1_struct_0(esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_48]), c_0_46]), c_0_47])])).
% 0.18/0.44  cnf(c_0_82, negated_conjecture, (k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))=k1_funct_1(X1,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))|u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.18/0.44  cnf(c_0_83, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])).
% 0.18/0.44  cnf(c_0_84, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)|k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))!=k1_funct_1(esk5_0,esk2_2(k4_tmap_1(esk3_0,esk4_0),esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_38]), c_0_81])).
% 0.18/0.44  cnf(c_0_85, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.44  cnf(c_0_86, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_39]), c_0_40])]), c_0_84])).
% 0.18/0.44  fof(c_0_87, plain, ![X19, X20, X21, X22, X23]:((~r2_funct_2(X19,X20,X21,X22)|(~m1_subset_1(X23,X19)|k1_funct_1(X21,X23)=k1_funct_1(X22,X23))|(~v1_funct_1(X22)|~v1_funct_2(X22,X19,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))&((m1_subset_1(esk1_4(X19,X20,X21,X22),X19)|r2_funct_2(X19,X20,X21,X22)|(~v1_funct_1(X22)|~v1_funct_2(X22,X19,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))&(k1_funct_1(X21,esk1_4(X19,X20,X21,X22))!=k1_funct_1(X22,esk1_4(X19,X20,X21,X22))|r2_funct_2(X19,X20,X21,X22)|(~v1_funct_1(X22)|~v1_funct_2(X22,X19,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).
% 0.18/0.44  cnf(c_0_88, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_89, negated_conjecture, (k4_tmap_1(esk3_0,esk4_0)=esk5_0|u1_struct_0(esk3_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_83])).
% 0.18/0.44  cnf(c_0_90, plain, (r2_funct_2(X2,X3,X1,X4)|k1_funct_1(X1,esk1_4(X2,X3,X1,X4))!=k1_funct_1(X4,esk1_4(X2,X3,X1,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.18/0.44  fof(c_0_91, plain, ![X30]:(v2_struct_0(X30)|~l1_struct_0(X30)|~v1_xboole_0(u1_struct_0(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.18/0.44  cnf(c_0_92, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.18/0.44  cnf(c_0_93, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_90])).
% 0.18/0.44  cnf(c_0_94, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.18/0.44  cnf(c_0_95, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_46]), c_0_35]), c_0_34])])).
% 0.18/0.44  cnf(c_0_96, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.44  fof(c_0_97, plain, ![X29]:(~l1_pre_topc(X29)|l1_struct_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.18/0.44  cnf(c_0_98, negated_conjecture, (~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96])]), c_0_22])).
% 0.18/0.44  cnf(c_0_99, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.18/0.44  cnf(c_0_100, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_21])]), ['proof']).
% 0.18/0.44  # SZS output end CNFRefutation
% 0.18/0.44  # Proof object total steps             : 101
% 0.18/0.44  # Proof object clause steps            : 73
% 0.18/0.44  # Proof object formula steps           : 28
% 0.18/0.44  # Proof object conjectures             : 54
% 0.18/0.44  # Proof object clause conjectures      : 51
% 0.18/0.44  # Proof object formula conjectures     : 3
% 0.18/0.44  # Proof object initial clauses used    : 29
% 0.18/0.44  # Proof object initial formulas used   : 14
% 0.18/0.44  # Proof object generating inferences   : 43
% 0.18/0.44  # Proof object simplifying inferences  : 102
% 0.18/0.44  # Training examples: 0 positive, 0 negative
% 0.18/0.44  # Parsed axioms                        : 14
% 0.18/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.44  # Initial clauses                      : 37
% 0.18/0.44  # Removed in clause preprocessing      : 0
% 0.18/0.44  # Initial clauses in saturation        : 37
% 0.18/0.44  # Processed clauses                    : 492
% 0.18/0.44  # ...of these trivial                  : 2
% 0.18/0.44  # ...subsumed                          : 216
% 0.18/0.44  # ...remaining for further processing  : 274
% 0.18/0.44  # Other redundant clauses eliminated   : 4
% 0.18/0.44  # Clauses deleted for lack of memory   : 0
% 0.18/0.44  # Backward-subsumed                    : 33
% 0.18/0.44  # Backward-rewritten                   : 89
% 0.18/0.44  # Generated clauses                    : 1420
% 0.18/0.44  # ...of the previous two non-trivial   : 1323
% 0.18/0.44  # Contextual simplify-reflections      : 26
% 0.18/0.44  # Paramodulations                      : 1400
% 0.18/0.44  # Factorizations                       : 10
% 0.18/0.44  # Equation resolutions                 : 10
% 0.18/0.44  # Propositional unsat checks           : 0
% 0.18/0.44  #    Propositional check models        : 0
% 0.18/0.44  #    Propositional check unsatisfiable : 0
% 0.18/0.44  #    Propositional clauses             : 0
% 0.18/0.44  #    Propositional clauses after purity: 0
% 0.18/0.44  #    Propositional unsat core size     : 0
% 0.18/0.44  #    Propositional preprocessing time  : 0.000
% 0.18/0.44  #    Propositional encoding time       : 0.000
% 0.18/0.44  #    Propositional solver time         : 0.000
% 0.18/0.44  #    Success case prop preproc time    : 0.000
% 0.18/0.44  #    Success case prop encoding time   : 0.000
% 0.18/0.44  #    Success case prop solver time     : 0.000
% 0.18/0.44  # Current number of processed clauses  : 114
% 0.18/0.44  #    Positive orientable unit clauses  : 10
% 0.18/0.44  #    Positive unorientable unit clauses: 0
% 0.18/0.44  #    Negative unit clauses             : 3
% 0.18/0.44  #    Non-unit-clauses                  : 101
% 0.18/0.44  # Current number of unprocessed clauses: 877
% 0.18/0.44  # ...number of literals in the above   : 9953
% 0.18/0.44  # Current number of archived formulas  : 0
% 0.18/0.44  # Current number of archived clauses   : 158
% 0.18/0.44  # Clause-clause subsumption calls (NU) : 13960
% 0.18/0.44  # Rec. Clause-clause subsumption calls : 1884
% 0.18/0.44  # Non-unit clause-clause subsumptions  : 270
% 0.18/0.44  # Unit Clause-clause subsumption calls : 70
% 0.18/0.44  # Rewrite failures with RHS unbound    : 0
% 0.18/0.44  # BW rewrite match attempts            : 2
% 0.18/0.44  # BW rewrite match successes           : 1
% 0.18/0.44  # Condensation attempts                : 0
% 0.18/0.44  # Condensation successes               : 0
% 0.18/0.44  # Termbank termtop insertions          : 55298
% 0.18/0.44  
% 0.18/0.44  # -------------------------------------------------
% 0.18/0.44  # User time                : 0.102 s
% 0.18/0.44  # System time              : 0.008 s
% 0.18/0.44  # Total time               : 0.110 s
% 0.18/0.44  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
