%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:11 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  162 (28900742 expanded)
%              Number of clauses        :  137 (9947192 expanded)
%              Number of leaves         :   12 (7226087 expanded)
%              Depth                    :   46
%              Number of atoms          :  583 (224932458 expanded)
%              Number of equality atoms :  156 (25257876 expanded)
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

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

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
    ! [X30,X31] :
      ( ( v1_funct_1(k4_tmap_1(X30,X31))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X31,X30) )
      & ( v1_funct_2(k4_tmap_1(X30,X31),u1_struct_0(X31),u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X31,X30) )
      & ( m1_subset_1(k4_tmap_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30))))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X31,X30) ) ) ),
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
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
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
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k1_relset_1(X13,X14,X15) = k1_relat_1(X15) ) ),
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
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_relat_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_27,plain,(
    ! [X11,X12] : v1_relat_1(k2_zfmisc_1(X11,X12)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_28,plain,(
    ! [X23,X24,X25] :
      ( ( r1_tarski(k1_relat_1(X23),k1_relat_1(X24))
        | ~ r1_tarski(X23,X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(X25,k1_relat_1(X23))
        | k1_funct_1(X23,X25) = k1_funct_1(X24,X25)
        | ~ r1_tarski(X23,X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( r2_hidden(esk1_2(X23,X24),k1_relat_1(X23))
        | ~ r1_tarski(k1_relat_1(X23),k1_relat_1(X24))
        | r1_tarski(X23,X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( k1_funct_1(X23,esk1_2(X23,X24)) != k1_funct_1(X24,esk1_2(X23,X24))
        | ~ r1_tarski(k1_relat_1(X23),k1_relat_1(X24))
        | r1_tarski(X23,X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_grfunc_1])])])])])).

cnf(c_0_29,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk3_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_31,plain,
    ( v1_funct_1(k4_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_36,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))
    | r1_tarski(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(k4_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk3_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_24])])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(k4_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(k4_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_24]),c_0_33])])).

cnf(c_0_41,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0) = u1_struct_0(esk3_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_34]),c_0_35])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_43,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | m1_subset_1(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r2_hidden(esk1_2(X1,k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(X1))
    | r1_tarski(X1,k4_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(esk4_0) = u1_struct_0(esk3_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_41]),c_0_34])])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_34]),c_0_33])])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_42])).

fof(c_0_49,plain,(
    ! [X27,X28,X29] :
      ( v2_struct_0(X27)
      | ~ l1_pre_topc(X27)
      | v2_struct_0(X28)
      | ~ m1_pre_topc(X28,X27)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | m1_subset_1(X29,u1_struct_0(X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r2_hidden(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48])])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | m1_subset_1(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_55,plain,(
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

cnf(c_0_56,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v2_struct_0(X1)
    | m1_subset_1(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(X1))
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_funct_1(k4_tmap_1(X1,X2),X3) = X3
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | m1_subset_1(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0))
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_17]),c_0_19])]),c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( X1 = k1_funct_1(esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_60,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,X1),esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | u1_struct_0(esk2_0) = k1_xboole_0
    | v2_struct_0(X1)
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ r2_hidden(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_61,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_51])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_63,plain,
    ( k1_funct_1(X2,X1) = k1_funct_1(X3,X1)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r1_tarski(X2,X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r2_hidden(esk1_2(X1,esk4_0),k1_relat_1(X1))
    | r1_tarski(X1,esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | k1_funct_1(X1,esk1_2(X1,X2)) != k1_funct_1(X2,esk1_2(X1,X2))
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_66,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_51]),c_0_17])]),c_0_54])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = k1_funct_1(X2,X1)
    | u1_struct_0(esk2_0) = k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(esk4_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_38]),c_0_39]),c_0_40]),c_0_48])])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | ~ r1_tarski(k1_relat_1(esk4_0),k1_relat_1(k4_tmap_1(esk2_0,esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_39]),c_0_46]),c_0_40]),c_0_47])]),c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_48]),c_0_46]),c_0_47])])).

cnf(c_0_73,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)) = k1_funct_1(X1,esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0))
    | u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_38]),c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)) = k1_funct_1(esk4_0,esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0))
    | u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_39]),c_0_40])])).

cnf(c_0_76,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(u1_struct_0(esk3_0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_77,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_75]),c_0_46]),c_0_39]),c_0_47]),c_0_40])])).

cnf(c_0_79,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(u1_struct_0(esk3_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_48]),c_0_46]),c_0_47])])).

cnf(c_0_80,negated_conjecture,
    ( k4_tmap_1(esk2_0,esk3_0) = esk4_0
    | u1_struct_0(esk2_0) = k1_xboole_0
    | ~ r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_38]),c_0_79])).

fof(c_0_82,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ r2_funct_2(X19,X20,X21,X22)
        | X21 = X22
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X21 != X22
        | r2_funct_2(X19,X20,X21,X22)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_83,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_84,negated_conjecture,
    ( k4_tmap_1(esk2_0,esk3_0) = esk4_0
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_88,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_89,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_46]),c_0_35]),c_0_34])])).

cnf(c_0_90,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_91,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_89])).

cnf(c_0_94,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])])).

cnf(c_0_96,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_89])).

cnf(c_0_100,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_89])).

cnf(c_0_101,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_95])).

cnf(c_0_104,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,X1),X2) = X2
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X2,k1_xboole_0)
    | ~ r2_hidden(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_89]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_105,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk4_0,X1),k1_xboole_0)
    | r1_tarski(esk4_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_101]),c_0_46]),c_0_47])])).

cnf(c_0_106,negated_conjecture,
    ( k1_relat_1(k4_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_102]),c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = X1
    | ~ m1_subset_1(X1,k1_xboole_0)
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_59,c_0_89])).

cnf(c_0_108,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1) = X1
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_95]),c_0_17])]),c_0_54]),c_0_50])).

cnf(c_0_109,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),k1_xboole_0)
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_39]),c_0_40]),c_0_48])])).

cnf(c_0_110,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = X1
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_95]),c_0_50])).

cnf(c_0_111,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_2(X1,esk4_0),k1_relat_1(X1))
    | r1_tarski(X1,esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_101]),c_0_46]),c_0_47])])).

cnf(c_0_112,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_109])).

cnf(c_0_114,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_101]),c_0_46]),c_0_47])])).

cnf(c_0_115,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_106]),c_0_39]),c_0_40]),c_0_48])])).

cnf(c_0_116,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | ~ r1_tarski(k1_relat_1(esk4_0),k1_relat_1(k4_tmap_1(esk2_0,esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_112]),c_0_39]),c_0_46]),c_0_40]),c_0_47])]),c_0_113])).

cnf(c_0_117,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k1_relat_1(esk4_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_48]),c_0_46]),c_0_47])])).

cnf(c_0_118,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | esk4_0 = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | esk4_0 = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_115])).

cnf(c_0_120,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_101]),c_0_46]),c_0_47])])).

cnf(c_0_121,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_106]),c_0_117])).

cnf(c_0_122,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_118]),c_0_46]),c_0_39]),c_0_47]),c_0_40])]),c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_48]),c_0_46]),c_0_47])])).

cnf(c_0_124,negated_conjecture,
    ( k4_tmap_1(esk2_0,esk3_0) = esk4_0
    | esk4_0 = k1_xboole_0
    | ~ r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_121])).

cnf(c_0_125,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_106]),c_0_123])).

cnf(c_0_126,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_89])).

cnf(c_0_127,negated_conjecture,
    ( k4_tmap_1(esk2_0,esk3_0) = esk4_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_128,negated_conjecture,
    ( k4_tmap_1(esk2_0,esk3_0) = k1_xboole_0
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_99]),c_0_100])])).

cnf(c_0_129,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_130,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_126,c_0_128])).

cnf(c_0_131,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_87]),c_0_46]),c_0_93]),c_0_92])])).

cnf(c_0_132,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_133,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_131])).

cnf(c_0_134,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_93,c_0_131])).

cnf(c_0_135,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_92,c_0_131])).

cnf(c_0_136,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_87]),c_0_133]),c_0_134]),c_0_135])])).

cnf(c_0_137,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_99,c_0_136])).

cnf(c_0_138,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_100,c_0_136])).

cnf(c_0_139,negated_conjecture,
    ( k1_relat_1(k4_tmap_1(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_137]),c_0_138])])).

cnf(c_0_140,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_141,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_134,c_0_136])).

cnf(c_0_142,negated_conjecture,
    ( r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),X1),k1_xboole_0)
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_139]),c_0_39]),c_0_40])])).

cnf(c_0_143,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_140]),c_0_141])])).

cnf(c_0_144,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_131])).

cnf(c_0_145,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1) = X1
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_136]),c_0_17])]),c_0_54]),c_0_50])).

cnf(c_0_146,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,X1) = X1
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_131]),c_0_136]),c_0_50])).

cnf(c_0_147,negated_conjecture,
    ( r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_133]),c_0_144]),c_0_48])])).

cnf(c_0_148,negated_conjecture,
    ( r2_hidden(esk1_2(X1,k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(X1))
    | r1_tarski(X1,k4_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_139]),c_0_39]),c_0_40])])).

cnf(c_0_149,negated_conjecture,
    ( r1_tarski(k4_tmap_1(esk2_0,esk3_0),X1)
    | k1_funct_1(X1,esk1_2(k4_tmap_1(esk2_0,esk3_0),X1)) != esk1_2(k4_tmap_1(esk2_0,esk3_0),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_145]),c_0_39]),c_0_40]),c_0_139])]),c_0_142])).

cnf(c_0_150,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk1_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)) = esk1_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_151,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_143]),c_0_133]),c_0_144]),c_0_48])])).

cnf(c_0_152,negated_conjecture,
    ( r1_tarski(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_150]),c_0_133]),c_0_144]),c_0_143]),c_0_48])])).

cnf(c_0_153,negated_conjecture,
    ( r1_tarski(X1,k4_tmap_1(esk2_0,esk3_0))
    | k1_funct_1(X1,esk1_2(X1,k4_tmap_1(esk2_0,esk3_0))) != esk1_2(X1,k4_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk1_2(X1,k4_tmap_1(esk2_0,esk3_0)),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_145]),c_0_39]),c_0_40]),c_0_139])])).

cnf(c_0_154,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk1_2(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_2(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0))
    | r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_146,c_0_151])).

cnf(c_0_155,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k4_tmap_1(esk2_0,esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_126,c_0_131])).

cnf(c_0_156,negated_conjecture,
    ( k4_tmap_1(esk2_0,esk3_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_152])).

cnf(c_0_157,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_151]),c_0_133]),c_0_144]),c_0_143]),c_0_48])]),c_0_154])).

cnf(c_0_158,negated_conjecture,
    ( ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1(esk2_0,esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_155,c_0_136])).

cnf(c_0_159,negated_conjecture,
    ( k4_tmap_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_156,c_0_157])])).

cnf(c_0_160,negated_conjecture,
    ( ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_158,c_0_159])).

cnf(c_0_161,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_87]),c_0_133]),c_0_141]),c_0_140])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:51:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.029 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t96_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_tmap_1)).
% 0.20/0.41  fof(dt_k4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k4_tmap_1(X1,X2))&v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 0.20/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.41  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.41  fof(t8_grfunc_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,X2)<=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_grfunc_1)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.41  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.20/0.41  fof(t95_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,u1_struct_0(X2))=>k1_funct_1(k4_tmap_1(X1,X2),X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tmap_1)).
% 0.20/0.41  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.20/0.41  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t96_tmap_1])).
% 0.20/0.41  fof(c_0_13, plain, ![X30, X31]:(((v1_funct_1(k4_tmap_1(X30,X31))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_pre_topc(X31,X30)))&(v1_funct_2(k4_tmap_1(X30,X31),u1_struct_0(X31),u1_struct_0(X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_pre_topc(X31,X30))))&(m1_subset_1(k4_tmap_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30))))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_pre_topc(X31,X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).
% 0.20/0.41  fof(c_0_14, negated_conjecture, ![X38]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&((~m1_subset_1(X38,u1_struct_0(esk2_0))|(~r2_hidden(X38,u1_struct_0(esk3_0))|X38=k1_funct_1(esk4_0,X38)))&~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).
% 0.20/0.41  fof(c_0_15, plain, ![X16, X17, X18]:((((~v1_funct_2(X18,X16,X17)|X16=k1_relset_1(X16,X17,X18)|X17=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(X16!=k1_relset_1(X16,X17,X18)|v1_funct_2(X18,X16,X17)|X17=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))&((~v1_funct_2(X18,X16,X17)|X16=k1_relset_1(X16,X17,X18)|X16!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(X16!=k1_relset_1(X16,X17,X18)|v1_funct_2(X18,X16,X17)|X16!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))&((~v1_funct_2(X18,X16,X17)|X18=k1_xboole_0|X16=k1_xboole_0|X17!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(X18!=k1_xboole_0|v1_funct_2(X18,X16,X17)|X16=k1_xboole_0|X17!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.41  cnf(c_0_16, plain, (m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_17, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_21, plain, (v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  fof(c_0_22, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|k1_relset_1(X13,X14,X15)=k1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.41  cnf(c_0_23, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (v1_funct_2(k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.41  fof(c_0_26, plain, ![X9, X10]:(~v1_relat_1(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_relat_1(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.41  fof(c_0_27, plain, ![X11, X12]:v1_relat_1(k2_zfmisc_1(X11,X12)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.41  fof(c_0_28, plain, ![X23, X24, X25]:(((r1_tarski(k1_relat_1(X23),k1_relat_1(X24))|~r1_tarski(X23,X24)|(~v1_relat_1(X24)|~v1_funct_1(X24))|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(~r2_hidden(X25,k1_relat_1(X23))|k1_funct_1(X23,X25)=k1_funct_1(X24,X25)|~r1_tarski(X23,X24)|(~v1_relat_1(X24)|~v1_funct_1(X24))|(~v1_relat_1(X23)|~v1_funct_1(X23))))&((r2_hidden(esk1_2(X23,X24),k1_relat_1(X23))|~r1_tarski(k1_relat_1(X23),k1_relat_1(X24))|r1_tarski(X23,X24)|(~v1_relat_1(X24)|~v1_funct_1(X24))|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(k1_funct_1(X23,esk1_2(X23,X24))!=k1_funct_1(X24,esk1_2(X23,X24))|~r1_tarski(k1_relat_1(X23),k1_relat_1(X24))|r1_tarski(X23,X24)|(~v1_relat_1(X24)|~v1_funct_1(X24))|(~v1_relat_1(X23)|~v1_funct_1(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_grfunc_1])])])])])).
% 0.20/0.41  cnf(c_0_29, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0))=u1_struct_0(esk3_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.20/0.41  cnf(c_0_31, plain, (v1_funct_1(k4_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_32, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_33, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  fof(c_0_36, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  cnf(c_0_37, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))|r1_tarski(X1,X2)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (k1_relat_1(k4_tmap_1(esk2_0,esk3_0))=u1_struct_0(esk3_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_24])])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (v1_funct_1(k4_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (v1_relat_1(k4_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_24]), c_0_33])])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0)=u1_struct_0(esk3_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_34]), c_0_35])])).
% 0.20/0.41  cnf(c_0_42, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.41  fof(c_0_43, plain, ![X7, X8]:(~r2_hidden(X7,X8)|m1_subset_1(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r2_hidden(esk1_2(X1,k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(X1))|r1_tarski(X1,k4_tmap_1(esk2_0,esk3_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (k1_relat_1(esk4_0)=u1_struct_0(esk3_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_41]), c_0_34])])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_34]), c_0_33])])).
% 0.20/0.41  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_42])).
% 0.20/0.41  fof(c_0_49, plain, ![X27, X28, X29]:(v2_struct_0(X27)|~l1_pre_topc(X27)|(v2_struct_0(X28)|~m1_pre_topc(X28,X27)|(~m1_subset_1(X29,u1_struct_0(X28))|m1_subset_1(X29,u1_struct_0(X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.20/0.41  cnf(c_0_50, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r2_hidden(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_48])])).
% 0.20/0.41  cnf(c_0_52, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|m1_subset_1(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  fof(c_0_55, plain, ![X32, X33, X34]:(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|(v2_struct_0(X33)|~m1_pre_topc(X33,X32)|(~m1_subset_1(X34,u1_struct_0(X32))|(~r2_hidden(X34,u1_struct_0(X33))|k1_funct_1(k4_tmap_1(X32,X33),X34)=X34)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v2_struct_0(X1)|m1_subset_1(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(X1))|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.20/0.41  cnf(c_0_57, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_funct_1(k4_tmap_1(X1,X2),X3)=X3|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|m1_subset_1(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0))|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_17]), c_0_19])]), c_0_20])).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (X1=k1_funct_1(esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,X1),esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))|u1_struct_0(esk2_0)=k1_xboole_0|v2_struct_0(X1)|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,esk2_0)|~r2_hidden(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (k1_funct_1(esk4_0,esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))|u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))|~m1_subset_1(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_59, c_0_51])).
% 0.20/0.41  cnf(c_0_62, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.41  cnf(c_0_63, plain, (k1_funct_1(X2,X1)=k1_funct_1(X3,X1)|~r2_hidden(X1,k1_relat_1(X2))|~r1_tarski(X2,X3)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r2_hidden(esk1_2(X1,esk4_0),k1_relat_1(X1))|r1_tarski(X1,esk4_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_45]), c_0_46]), c_0_47])])).
% 0.20/0.41  cnf(c_0_65, plain, (r1_tarski(X1,X2)|k1_funct_1(X1,esk1_2(X1,X2))!=k1_funct_1(X2,esk1_2(X1,X2))|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))|u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_51]), c_0_17])]), c_0_54])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (k1_funct_1(esk4_0,esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))|u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_61, c_0_58])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(k1_relat_1(X1),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_45]), c_0_46]), c_0_47])])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (k1_funct_1(esk4_0,X1)=k1_funct_1(X2,X1)|u1_struct_0(esk2_0)=k1_xboole_0|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,u1_struct_0(esk3_0))|~r1_tarski(esk4_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_45]), c_0_46]), c_0_47])])).
% 0.20/0.41  cnf(c_0_70, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_38]), c_0_39]), c_0_40]), c_0_48])])).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))|~r1_tarski(k1_relat_1(esk4_0),k1_relat_1(k4_tmap_1(esk2_0,esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_39]), c_0_46]), c_0_40]), c_0_47])]), c_0_67])).
% 0.20/0.41  cnf(c_0_72, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(k1_relat_1(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_48]), c_0_46]), c_0_47])])).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (k1_funct_1(esk4_0,esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0))=k1_funct_1(X1,esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0))|u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.41  cnf(c_0_74, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_38]), c_0_72])).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0))=k1_funct_1(esk4_0,esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0))|u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_39]), c_0_40])])).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(u1_struct_0(esk3_0),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_45]), c_0_46]), c_0_47])])).
% 0.20/0.41  cnf(c_0_77, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.41  cnf(c_0_78, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)|~r1_tarski(k1_relat_1(k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_75]), c_0_46]), c_0_39]), c_0_47]), c_0_40])])).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(u1_struct_0(esk3_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_48]), c_0_46]), c_0_47])])).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (k4_tmap_1(esk2_0,esk3_0)=esk4_0|u1_struct_0(esk2_0)=k1_xboole_0|~r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_77, c_0_74])).
% 0.20/0.41  cnf(c_0_81, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_38]), c_0_79])).
% 0.20/0.41  fof(c_0_82, plain, ![X19, X20, X21, X22]:((~r2_funct_2(X19,X20,X21,X22)|X21=X22|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|~v1_funct_1(X22)|~v1_funct_2(X22,X19,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))&(X21!=X22|r2_funct_2(X19,X20,X21,X22)|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|~v1_funct_1(X22)|~v1_funct_2(X22,X19,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.20/0.41  cnf(c_0_83, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_84, negated_conjecture, (k4_tmap_1(esk2_0,esk3_0)=esk4_0|u1_struct_0(esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.20/0.41  cnf(c_0_85, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.41  cnf(c_0_86, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.41  cnf(c_0_87, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_85])).
% 0.20/0.41  cnf(c_0_88, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_89, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_46]), c_0_35]), c_0_34])])).
% 0.20/0.41  cnf(c_0_90, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_91, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_88])).
% 0.20/0.41  cnf(c_0_92, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),k1_xboole_0)))), inference(rw,[status(thm)],[c_0_34, c_0_89])).
% 0.20/0.41  cnf(c_0_93, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_35, c_0_89])).
% 0.20/0.41  cnf(c_0_94, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_90])).
% 0.20/0.41  cnf(c_0_95, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])])).
% 0.20/0.41  cnf(c_0_96, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_29, c_0_94])).
% 0.20/0.41  cnf(c_0_97, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_92, c_0_95])).
% 0.20/0.41  cnf(c_0_98, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_93, c_0_95])).
% 0.20/0.41  cnf(c_0_99, negated_conjecture, (m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),k1_xboole_0)))), inference(rw,[status(thm)],[c_0_24, c_0_89])).
% 0.20/0.41  cnf(c_0_100, negated_conjecture, (v1_funct_2(k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_25, c_0_89])).
% 0.20/0.41  cnf(c_0_101, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])).
% 0.20/0.41  cnf(c_0_102, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_99, c_0_95])).
% 0.20/0.41  cnf(c_0_103, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_100, c_0_95])).
% 0.20/0.41  cnf(c_0_104, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,X1),X2)=X2|v2_struct_0(X1)|~m1_pre_topc(X1,esk2_0)|~m1_subset_1(X2,k1_xboole_0)|~r2_hidden(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_89]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.41  cnf(c_0_105, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_2(esk4_0,X1),k1_xboole_0)|r1_tarski(esk4_0,X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_xboole_0,k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_101]), c_0_46]), c_0_47])])).
% 0.20/0.41  cnf(c_0_106, negated_conjecture, (k1_relat_1(k4_tmap_1(esk2_0,esk3_0))=k1_xboole_0|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_102]), c_0_103])).
% 0.20/0.41  cnf(c_0_107, negated_conjecture, (k1_funct_1(esk4_0,X1)=X1|~m1_subset_1(X1,k1_xboole_0)|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_59, c_0_89])).
% 0.20/0.41  cnf(c_0_108, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1)=X1|esk4_0=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_95]), c_0_17])]), c_0_54]), c_0_50])).
% 0.20/0.41  cnf(c_0_109, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),k1_xboole_0)|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_39]), c_0_40]), c_0_48])])).
% 0.20/0.41  cnf(c_0_110, negated_conjecture, (k1_funct_1(esk4_0,X1)=X1|esk4_0=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_95]), c_0_50])).
% 0.20/0.41  cnf(c_0_111, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_2(X1,esk4_0),k1_relat_1(X1))|r1_tarski(X1,esk4_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_101]), c_0_46]), c_0_47])])).
% 0.20/0.41  cnf(c_0_112, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))|esk4_0=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.20/0.41  cnf(c_0_113, negated_conjecture, (k1_funct_1(esk4_0,esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))|esk4_0=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_110, c_0_109])).
% 0.20/0.41  cnf(c_0_114, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k1_relat_1(X1),k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_101]), c_0_46]), c_0_47])])).
% 0.20/0.41  cnf(c_0_115, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0),k1_xboole_0)|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_106]), c_0_39]), c_0_40]), c_0_48])])).
% 0.20/0.41  cnf(c_0_116, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))|~r1_tarski(k1_relat_1(esk4_0),k1_relat_1(k4_tmap_1(esk2_0,esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_112]), c_0_39]), c_0_46]), c_0_40]), c_0_47])]), c_0_113])).
% 0.20/0.41  cnf(c_0_117, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k1_relat_1(esk4_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_48]), c_0_46]), c_0_47])])).
% 0.20/0.41  cnf(c_0_118, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)|esk4_0=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_108, c_0_115])).
% 0.20/0.41  cnf(c_0_119, negated_conjecture, (k1_funct_1(esk4_0,esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)|esk4_0=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_110, c_0_115])).
% 0.20/0.41  cnf(c_0_120, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k1_xboole_0,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_101]), c_0_46]), c_0_47])])).
% 0.20/0.41  cnf(c_0_121, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_106]), c_0_117])).
% 0.20/0.41  cnf(c_0_122, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)|~r1_tarski(k1_relat_1(k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_118]), c_0_46]), c_0_39]), c_0_47]), c_0_40])]), c_0_119])).
% 0.20/0.41  cnf(c_0_123, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k1_xboole_0,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_48]), c_0_46]), c_0_47])])).
% 0.20/0.41  cnf(c_0_124, negated_conjecture, (k4_tmap_1(esk2_0,esk3_0)=esk4_0|esk4_0=k1_xboole_0|~r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_77, c_0_121])).
% 0.20/0.41  cnf(c_0_125, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_106]), c_0_123])).
% 0.20/0.41  cnf(c_0_126, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_83, c_0_89])).
% 0.20/0.41  cnf(c_0_127, negated_conjecture, (k4_tmap_1(esk2_0,esk3_0)=esk4_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 0.20/0.41  cnf(c_0_128, negated_conjecture, (k4_tmap_1(esk2_0,esk3_0)=k1_xboole_0|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_99]), c_0_100])])).
% 0.20/0.41  cnf(c_0_129, negated_conjecture, (esk4_0=k1_xboole_0|~r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 0.20/0.41  cnf(c_0_130, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|~r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_126, c_0_128])).
% 0.20/0.41  cnf(c_0_131, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_87]), c_0_46]), c_0_93]), c_0_92])])).
% 0.20/0.41  cnf(c_0_132, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|~r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_130, c_0_131])).
% 0.20/0.41  cnf(c_0_133, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_46, c_0_131])).
% 0.20/0.41  cnf(c_0_134, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_93, c_0_131])).
% 0.20/0.41  cnf(c_0_135, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),k1_xboole_0)))), inference(rw,[status(thm)],[c_0_92, c_0_131])).
% 0.20/0.41  cnf(c_0_136, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_87]), c_0_133]), c_0_134]), c_0_135])])).
% 0.20/0.41  cnf(c_0_137, negated_conjecture, (m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_99, c_0_136])).
% 0.20/0.41  cnf(c_0_138, negated_conjecture, (v1_funct_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_100, c_0_136])).
% 0.20/0.41  cnf(c_0_139, negated_conjecture, (k1_relat_1(k4_tmap_1(esk2_0,esk3_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_137]), c_0_138])])).
% 0.20/0.41  cnf(c_0_140, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_135, c_0_136])).
% 0.20/0.41  cnf(c_0_141, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_134, c_0_136])).
% 0.20/0.41  cnf(c_0_142, negated_conjecture, (r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),X1),k1_xboole_0)|r1_tarski(k4_tmap_1(esk2_0,esk3_0),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_xboole_0,k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_139]), c_0_39]), c_0_40])])).
% 0.20/0.41  cnf(c_0_143, negated_conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_140]), c_0_141])])).
% 0.20/0.41  cnf(c_0_144, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_47, c_0_131])).
% 0.20/0.41  cnf(c_0_145, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1)=X1|~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_136]), c_0_17])]), c_0_54]), c_0_50])).
% 0.20/0.41  cnf(c_0_146, negated_conjecture, (k1_funct_1(k1_xboole_0,X1)=X1|~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_131]), c_0_136]), c_0_50])).
% 0.20/0.41  cnf(c_0_147, negated_conjecture, (r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0),k1_xboole_0)|r1_tarski(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_133]), c_0_144]), c_0_48])])).
% 0.20/0.41  cnf(c_0_148, negated_conjecture, (r2_hidden(esk1_2(X1,k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(X1))|r1_tarski(X1,k4_tmap_1(esk2_0,esk3_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_139]), c_0_39]), c_0_40])])).
% 0.20/0.41  cnf(c_0_149, negated_conjecture, (r1_tarski(k4_tmap_1(esk2_0,esk3_0),X1)|k1_funct_1(X1,esk1_2(k4_tmap_1(esk2_0,esk3_0),X1))!=esk1_2(k4_tmap_1(esk2_0,esk3_0),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_xboole_0,k1_relat_1(X1))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_145]), c_0_39]), c_0_40]), c_0_139])]), c_0_142])).
% 0.20/0.41  cnf(c_0_150, negated_conjecture, (k1_funct_1(k1_xboole_0,esk1_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0))=esk1_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)|r1_tarski(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 0.20/0.41  cnf(c_0_151, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0)),k1_xboole_0)|r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_143]), c_0_133]), c_0_144]), c_0_48])])).
% 0.20/0.41  cnf(c_0_152, negated_conjecture, (r1_tarski(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_150]), c_0_133]), c_0_144]), c_0_143]), c_0_48])])).
% 0.20/0.41  cnf(c_0_153, negated_conjecture, (r1_tarski(X1,k4_tmap_1(esk2_0,esk3_0))|k1_funct_1(X1,esk1_2(X1,k4_tmap_1(esk2_0,esk3_0)))!=esk1_2(X1,k4_tmap_1(esk2_0,esk3_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(esk1_2(X1,k4_tmap_1(esk2_0,esk3_0)),k1_xboole_0)|~r1_tarski(k1_relat_1(X1),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_145]), c_0_39]), c_0_40]), c_0_139])])).
% 0.20/0.41  cnf(c_0_154, negated_conjecture, (k1_funct_1(k1_xboole_0,esk1_2(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_2(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0))|r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_146, c_0_151])).
% 0.20/0.41  cnf(c_0_155, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_126, c_0_131])).
% 0.20/0.41  cnf(c_0_156, negated_conjecture, (k4_tmap_1(esk2_0,esk3_0)=k1_xboole_0|~r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_77, c_0_152])).
% 0.20/0.41  cnf(c_0_157, negated_conjecture, (r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_151]), c_0_133]), c_0_144]), c_0_143]), c_0_48])]), c_0_154])).
% 0.20/0.41  cnf(c_0_158, negated_conjecture, (~r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_155, c_0_136])).
% 0.20/0.41  cnf(c_0_159, negated_conjecture, (k4_tmap_1(esk2_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_156, c_0_157])])).
% 0.20/0.41  cnf(c_0_160, negated_conjecture, (~r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_158, c_0_159])).
% 0.20/0.41  cnf(c_0_161, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_87]), c_0_133]), c_0_141]), c_0_140])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 162
% 0.20/0.41  # Proof object clause steps            : 137
% 0.20/0.41  # Proof object formula steps           : 25
% 0.20/0.41  # Proof object conjectures             : 116
% 0.20/0.41  # Proof object clause conjectures      : 113
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 29
% 0.20/0.41  # Proof object initial formulas used   : 12
% 0.20/0.41  # Proof object generating inferences   : 84
% 0.20/0.41  # Proof object simplifying inferences  : 220
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 12
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 34
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 34
% 0.20/0.41  # Processed clauses                    : 372
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 91
% 0.20/0.41  # ...remaining for further processing  : 281
% 0.20/0.41  # Other redundant clauses eliminated   : 8
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 42
% 0.20/0.41  # Backward-rewritten                   : 127
% 0.20/0.41  # Generated clauses                    : 544
% 0.20/0.41  # ...of the previous two non-trivial   : 458
% 0.20/0.41  # Contextual simplify-reflections      : 21
% 0.20/0.41  # Paramodulations                      : 536
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 9
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 72
% 0.20/0.41  #    Positive orientable unit clauses  : 14
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 3
% 0.20/0.41  #    Non-unit-clauses                  : 55
% 0.20/0.41  # Current number of unprocessed clauses: 86
% 0.20/0.41  # ...number of literals in the above   : 766
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 202
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 5364
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1190
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 150
% 0.20/0.41  # Unit Clause-clause subsumption calls : 95
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 12
% 0.20/0.41  # BW rewrite match successes           : 10
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 19508
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.059 s
% 0.20/0.41  # System time              : 0.008 s
% 0.20/0.41  # Total time               : 0.067 s
% 0.20/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
