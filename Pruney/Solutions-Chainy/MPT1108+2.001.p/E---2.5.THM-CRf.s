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
% DateTime   : Thu Dec  3 11:09:02 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  202 (3487 expanded)
%              Number of clauses        :  147 (1631 expanded)
%              Number of leaves         :   27 ( 864 expanded)
%              Depth                    :   24
%              Number of atoms          :  541 (11031 expanded)
%              Number of equality atoms :  123 (1335 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(redefinition_k5_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k5_relset_1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t33_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t103_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t30_pre_topc,conjecture,(
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
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( v1_funct_1(k5_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4))
                    & v1_funct_2(k5_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),u1_struct_0(k1_pre_topc(X1,X4)),u1_struct_0(X2))
                    & m1_subset_1(k5_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X4)),u1_struct_0(X2)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_pre_topc)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(cc6_funct_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & ~ v1_xboole_0(X3)
              & v1_funct_2(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(t130_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( k1_relset_1(X1,X2,X3) = X1
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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

fof(c_0_27,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_28,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X24,k1_zfmisc_1(X25))
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | m1_subset_1(X24,k1_zfmisc_1(X25)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_30,plain,(
    ! [X52,X53,X54,X55] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | k5_relset_1(X52,X53,X54,X55) = k7_relat_1(X54,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X41,X42] :
      ( ~ r2_hidden(X41,X42)
      | ~ r1_tarski(X42,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_34,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_35,plain,(
    ! [X21] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X21)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_36,plain,(
    ! [X56,X57,X58,X59] :
      ( ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X58)))
      | m1_subset_1(k5_relset_1(X56,X58,X59,X57),k1_zfmisc_1(k2_zfmisc_1(X57,X58))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_relset_1])])).

cnf(c_0_37,plain,
    ( k5_relset_1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_39,plain,(
    ! [X19,X20] :
      ( ( k2_zfmisc_1(X19,X20) != k1_xboole_0
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X19,X20) = k1_xboole_0 )
      & ( X20 != k1_xboole_0
        | k2_zfmisc_1(X19,X20) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( m1_subset_1(k5_relset_1(X2,X3,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k5_relset_1(X1,X2,k2_zfmisc_1(X1,X2),X3) = k7_relat_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_47,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_48,plain,(
    ! [X17,X18] :
      ( ~ v1_xboole_0(X17)
      | X17 = X18
      | ~ v1_xboole_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,esk1_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_51,plain,(
    ! [X22,X23] :
      ( ~ v1_xboole_0(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | v1_xboole_0(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_52,plain,
    ( m1_subset_1(k7_relat_1(k2_zfmisc_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_38]),c_0_45])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_46])).

fof(c_0_54,plain,(
    ! [X46,X47,X48] :
      ( ( v4_relat_1(X48,X46)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( v5_relat_1(X48,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_55,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | v1_relat_1(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_56,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ r1_tarski(X29,X30)
      | k7_relat_1(k7_relat_1(X31,X30),X29) = k7_relat_1(X31,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).

cnf(c_0_57,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( m1_subset_1(k7_relat_1(k2_zfmisc_1(X1,X2),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_63,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ v4_relat_1(X33,X32)
      | X33 = k7_relat_1(X33,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_64,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( k7_relat_1(k7_relat_1(X1,X3),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_68,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,plain,
    ( v1_xboole_0(k7_relat_1(k2_zfmisc_1(X1,X2),k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_60])])).

cnf(c_0_70,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_43])).

cnf(c_0_72,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_43])).

fof(c_0_73,negated_conjecture,(
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
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v1_funct_1(k5_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4))
                      & v1_funct_2(k5_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),u1_struct_0(k1_pre_topc(X1,X4)),u1_struct_0(X2))
                      & m1_subset_1(k5_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X4)),u1_struct_0(X2)))) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t30_pre_topc])).

cnf(c_0_74,plain,
    ( v4_relat_1(k2_zfmisc_1(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_38])).

cnf(c_0_75,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_38])).

cnf(c_0_76,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_77,plain,
    ( k7_relat_1(k2_zfmisc_1(X1,X2),k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_78,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])])).

fof(c_0_79,plain,(
    ! [X77,X78] :
      ( ~ l1_pre_topc(X77)
      | ~ m1_subset_1(X78,k1_zfmisc_1(u1_struct_0(X77)))
      | u1_struct_0(k1_pre_topc(X77,X78)) = X78 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

fof(c_0_80,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & l1_pre_topc(esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v1_funct_1(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))
      | ~ v1_funct_2(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0),u1_struct_0(k1_pre_topc(esk3_0,esk6_0)),u1_struct_0(esk4_0))
      | ~ m1_subset_1(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(esk3_0,esk6_0)),u1_struct_0(esk4_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_73])])])])).

fof(c_0_81,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ r1_tarski(X36,k1_relat_1(X37))
      | k1_relat_1(k7_relat_1(X37,X36)) = X36 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_82,plain,(
    ! [X60,X61,X62] :
      ( ( v1_funct_1(X62)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X60,X61)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
        | v1_xboole_0(X60)
        | v1_xboole_0(X61) )
      & ( ~ v1_xboole_0(X62)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X60,X61)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
        | v1_xboole_0(X60)
        | v1_xboole_0(X61) )
      & ( v1_funct_2(X62,X60,X61)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X60,X61)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
        | v1_xboole_0(X60)
        | v1_xboole_0(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).

fof(c_0_83,plain,(
    ! [X38] :
      ( ~ v1_xboole_0(X38)
      | v1_funct_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

fof(c_0_84,plain,(
    ! [X49,X50,X51] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | k1_relset_1(X49,X50,X51) = k1_relat_1(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_85,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_86,plain,
    ( k7_relat_1(k2_zfmisc_1(X1,X2),X1) = k2_zfmisc_1(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_74]),c_0_75])])).

cnf(c_0_87,plain,
    ( k7_relat_1(k2_zfmisc_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_xboole_0(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_75])])).

cnf(c_0_88,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

fof(c_0_91,plain,(
    ! [X39,X40] :
      ( ( v1_relat_1(k7_relat_1(X39,X40))
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( v1_funct_1(k7_relat_1(X39,X40))
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_93,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_94,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_95,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

fof(c_0_96,plain,(
    ! [X74,X75,X76] :
      ( ( v1_funct_1(X76)
        | k1_relset_1(X74,X75,X76) != X74
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))) )
      & ( v1_funct_2(X76,X74,X75)
        | k1_relset_1(X74,X75,X76) != X74
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))) )
      & ( m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75)))
        | k1_relset_1(X74,X75,X76) != X74
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_funct_2])])])).

cnf(c_0_97,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_98,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_99,plain,
    ( k1_xboole_0 = k2_zfmisc_1(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_funct_1(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))
    | ~ v1_funct_2(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0),u1_struct_0(k1_pre_topc(esk3_0,esk6_0)),u1_struct_0(esk4_0))
    | ~ m1_subset_1(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(esk3_0,esk6_0)),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_101,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk3_0,esk6_0)) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])])).

cnf(c_0_102,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_103,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_92])).

cnf(c_0_104,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_105,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_93,c_0_67])).

cnf(c_0_106,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_107,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_67])).

cnf(c_0_108,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relset_1(X2,X3,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_109,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_43])).

cnf(c_0_110,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_60])).

fof(c_0_111,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | r1_tarski(k7_relat_1(X35,X34),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_112,plain,
    ( k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)) = k2_zfmisc_1(X2,X3)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_113,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_99])).

cnf(c_0_114,negated_conjecture,
    ( ~ v1_funct_2(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0),esk6_0,u1_struct_0(esk4_0))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))
    | ~ m1_subset_1(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,u1_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101]),c_0_101])).

cnf(c_0_115,negated_conjecture,
    ( k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1) = k7_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_92])).

cnf(c_0_116,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104])])).

cnf(c_0_117,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_86]),c_0_75])])).

cnf(c_0_118,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_119,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110]),c_0_43])])])).

cnf(c_0_120,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_121,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_107])).

cnf(c_0_122,plain,
    ( k2_zfmisc_1(X1,X2) = X2
    | ~ v1_xboole_0(X3)
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_59]),c_0_113])).

cnf(c_0_123,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk5_0,esk6_0),esk6_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(k7_relat_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_115]),c_0_115]),c_0_116]),c_0_115])])).

cnf(c_0_124,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_92]),c_0_115])).

cnf(c_0_125,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_xboole_0(k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_117,c_0_59])).

cnf(c_0_126,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_60])])).

cnf(c_0_127,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_128,plain,
    ( v1_xboole_0(k7_relat_1(k2_zfmisc_1(X1,X2),X3))
    | ~ v1_xboole_0(k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_52])).

cnf(c_0_129,plain,
    ( k2_zfmisc_1(X1,X2) = X2
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_122,c_0_60])).

fof(c_0_130,plain,(
    ! [X66,X67,X68,X69] :
      ( ( v1_funct_1(k2_partfun1(X66,X67,X68,X69))
        | ~ v1_funct_1(X68)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) )
      & ( m1_subset_1(k2_partfun1(X66,X67,X68,X69),k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
        | ~ v1_funct_1(X68)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

fof(c_0_131,plain,(
    ! [X70,X71,X72,X73] :
      ( ~ v1_funct_1(X72)
      | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
      | k2_partfun1(X70,X71,X72,X73) = k7_relat_1(X72,X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_132,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk5_0,esk6_0),esk6_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_124])])).

cnf(c_0_133,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_98]),c_0_60])])).

cnf(c_0_134,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(ef,[status(thm)],[c_0_126])).

cnf(c_0_135,plain,
    ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_127])).

cnf(c_0_136,plain,
    ( v1_xboole_0(k7_relat_1(k2_zfmisc_1(X1,X2),X3))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_137,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

cnf(c_0_138,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_131])).

cnf(c_0_139,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk5_0,esk6_0),esk6_0,k1_relat_1(X1))
    | ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_140,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_134])).

cnf(c_0_141,plain,
    ( v1_xboole_0(k7_relat_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_135])).

cnf(c_0_142,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_92])).

cnf(c_0_143,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_136,c_0_86])).

cnf(c_0_144,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_92])).

cnf(c_0_145,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_146,negated_conjecture,
    ( m1_subset_1(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_92]),c_0_104])])).

cnf(c_0_147,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1) = k7_relat_1(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_92]),c_0_104])])).

cnf(c_0_148,negated_conjecture,
    ( v1_xboole_0(k7_relat_1(esk5_0,X1))
    | ~ v1_xboole_0(k2_zfmisc_1(X1,u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_124])).

cnf(c_0_149,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk5_0,esk6_0),esk6_0,k1_xboole_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_60])])).

cnf(c_0_150,plain,
    ( k7_relat_1(X1,X2) = X3
    | ~ v1_xboole_0(X3)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_141])).

cnf(c_0_151,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_143])).

cnf(c_0_152,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))),esk5_0) = k7_relat_1(X1,esk5_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_144])).

cnf(c_0_153,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_99,c_0_143])).

cnf(c_0_154,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_145,c_0_67])).

cnf(c_0_155,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk5_0,X1),k2_zfmisc_1(X1,u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_124])).

cnf(c_0_156,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_92])).

cnf(c_0_157,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_146,c_0_147])).

fof(c_0_158,plain,(
    ! [X63,X64,X65] :
      ( ( ~ v1_funct_2(X65,X63,X64)
        | X63 = k1_relset_1(X63,X64,X65)
        | X64 = k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( X63 != k1_relset_1(X63,X64,X65)
        | v1_funct_2(X65,X63,X64)
        | X64 = k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( ~ v1_funct_2(X65,X63,X64)
        | X63 = k1_relset_1(X63,X64,X65)
        | X63 != k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( X63 != k1_relset_1(X63,X64,X65)
        | v1_funct_2(X65,X63,X64)
        | X63 != k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( ~ v1_funct_2(X65,X63,X64)
        | X65 = k1_xboole_0
        | X63 = k1_xboole_0
        | X64 != k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( X65 != k1_xboole_0
        | v1_funct_2(X65,X63,X64)
        | X63 = k1_xboole_0
        | X64 != k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_159,negated_conjecture,
    ( v1_xboole_0(k7_relat_1(esk5_0,X1))
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_148,c_0_59])).

cnf(c_0_160,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(k7_relat_1(X1,X2),esk6_0),esk6_0,k1_xboole_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_150]),c_0_151])).

cnf(c_0_161,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk5_0,k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))),esk5_0) = k7_relat_1(esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_152,c_0_103])).

cnf(c_0_162,negated_conjecture,
    ( v1_xboole_0(k7_relat_1(esk5_0,k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_153]),c_0_60])])).

cnf(c_0_163,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k2_zfmisc_1(X1,u1_struct_0(esk4_0))
    | ~ v1_xboole_0(k2_zfmisc_1(X1,u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_154,c_0_155])).

cnf(c_0_164,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_98])).

cnf(c_0_165,plain,
    ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_107,c_0_141])).

cnf(c_0_166,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_xboole_0(k2_zfmisc_1(X3,X4))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_150])).

cnf(c_0_167,negated_conjecture,
    ( r1_tarski(esk6_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_89])).

cnf(c_0_168,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk5_0,X1)) = X1
    | ~ r1_tarski(X1,k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_156]),c_0_103])])).

cnf(c_0_169,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk5_0,X1)) = k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k7_relat_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_157])).

cnf(c_0_170,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_158])).

cnf(c_0_171,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_172,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(X1,X2),esk6_0,u1_struct_0(esk4_0))
    | ~ v1_xboole_0(k7_relat_1(esk5_0,esk6_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_132,c_0_150])).

cnf(c_0_173,negated_conjecture,
    ( v1_xboole_0(k7_relat_1(esk5_0,X1))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_98]),c_0_60])])).

cnf(c_0_174,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(k7_relat_1(esk5_0,esk5_0),esk6_0),esk6_0,k1_xboole_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_161]),c_0_162])).

cnf(c_0_175,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k2_zfmisc_1(X1,u1_struct_0(esk4_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_163,c_0_113])).

cnf(c_0_176,plain,
    ( v4_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_164,c_0_165])).

cnf(c_0_177,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_53]),c_0_60])])).

cnf(c_0_178,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,u1_struct_0(esk3_0)),esk6_0) = k7_relat_1(X1,esk6_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_167])).

cnf(c_0_179,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k7_relat_1(esk5_0,X1)) = X1
    | ~ r1_tarski(X1,k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_168,c_0_169])).

cnf(c_0_180,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = u1_struct_0(esk3_0)
    | u1_struct_0(esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_171]),c_0_92])])).

cnf(c_0_181,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(X1,X2),esk6_0,k7_relat_1(X3,X4))
    | ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_150]),c_0_173])).

cnf(c_0_182,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(k2_zfmisc_1(esk5_0,u1_struct_0(esk4_0)),esk6_0),esk6_0,k1_xboole_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_175]),c_0_151])).

cnf(c_0_183,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_176]),c_0_177])).

cnf(c_0_184,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,u1_struct_0(esk3_0)),esk6_0) = k7_relat_1(X1,esk6_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_178,c_0_121])).

cnf(c_0_185,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k7_relat_1(esk5_0,X1)) = k1_relset_1(X1,u1_struct_0(esk4_0),k7_relat_1(esk5_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_124]),c_0_169])).

cnf(c_0_186,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k7_relat_1(esk5_0,X1)) = X1
    | u1_struct_0(esk4_0) = k1_xboole_0
    | ~ r1_tarski(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_179,c_0_180])).

cnf(c_0_187,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(X1,X2),esk6_0,k1_xboole_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_78]),c_0_60])])).

cnf(c_0_188,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_158])).

cnf(c_0_189,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(u1_struct_0(esk4_0),esk6_0),esk6_0,k1_xboole_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_182,c_0_129])).

cnf(c_0_190,negated_conjecture,
    ( k7_relat_1(X1,esk6_0) = k7_relat_1(X1,u1_struct_0(esk3_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_183,c_0_184])).

cnf(c_0_191,negated_conjecture,
    ( v1_funct_2(k7_relat_1(esk5_0,X1),X1,u1_struct_0(esk4_0))
    | k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k7_relat_1(esk5_0,X1)) != X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_185]),c_0_116]),c_0_124])])).

cnf(c_0_192,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k7_relat_1(esk5_0,esk6_0)) = esk6_0
    | u1_struct_0(esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_186,c_0_167])).

cnf(c_0_193,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,esk6_0,k1_xboole_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187,c_0_78]),c_0_60])])).

cnf(c_0_194,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_188])]),c_0_98]),c_0_43])])).

cnf(c_0_195,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)),esk6_0,k1_xboole_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_189,c_0_190])).

cnf(c_0_196,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_192]),c_0_132])).

cnf(c_0_197,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_193,c_0_194])).

cnf(c_0_198,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,esk6_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_195,c_0_196]),c_0_78]),c_0_196]),c_0_60])])).

cnf(c_0_199,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_197,c_0_196]),c_0_60])])).

cnf(c_0_200,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[c_0_119,c_0_140])).

cnf(c_0_201,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_198,c_0_199]),c_0_200])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:11:32 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 1.93/2.16  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 1.93/2.16  # and selection function SelectCQIPrecWNTNp.
% 1.93/2.16  #
% 1.93/2.16  # Preprocessing time       : 0.029 s
% 1.93/2.16  # Presaturation interreduction done
% 1.93/2.16  
% 1.93/2.16  # Proof found!
% 1.93/2.16  # SZS status Theorem
% 1.93/2.16  # SZS output start CNFRefutation
% 1.93/2.16  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.93/2.16  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.93/2.16  fof(redefinition_k5_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k5_relset_1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.93/2.16  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.93/2.16  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.93/2.16  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.93/2.16  fof(t33_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 1.93/2.16  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.93/2.16  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.93/2.16  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.93/2.16  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 1.93/2.16  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.93/2.16  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.93/2.16  fof(t103_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 1.93/2.16  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.93/2.16  fof(t30_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:((~(v2_struct_0(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((v1_funct_1(k5_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4))&v1_funct_2(k5_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),u1_struct_0(k1_pre_topc(X1,X4)),u1_struct_0(X2)))&m1_subset_1(k5_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X4)),u1_struct_0(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_pre_topc)).
% 1.93/2.16  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 1.93/2.16  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 1.93/2.16  fof(cc6_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&~(v1_xboole_0(X3)))&v1_funct_2(X3,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 1.93/2.16  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.93/2.16  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.93/2.16  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 1.93/2.16  fof(t130_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(k1_relset_1(X1,X2,X3)=X1=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 1.93/2.16  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.93/2.16  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 1.93/2.16  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 1.93/2.16  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 1.93/2.16  fof(c_0_27, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.93/2.16  fof(c_0_28, plain, ![X24, X25]:((~m1_subset_1(X24,k1_zfmisc_1(X25))|r1_tarski(X24,X25))&(~r1_tarski(X24,X25)|m1_subset_1(X24,k1_zfmisc_1(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.93/2.16  cnf(c_0_29, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.93/2.16  fof(c_0_30, plain, ![X52, X53, X54, X55]:(~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|k5_relset_1(X52,X53,X54,X55)=k7_relat_1(X54,X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).
% 1.93/2.16  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.93/2.16  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_29])).
% 1.93/2.16  fof(c_0_33, plain, ![X41, X42]:(~r2_hidden(X41,X42)|~r1_tarski(X42,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 1.93/2.16  fof(c_0_34, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 1.93/2.16  fof(c_0_35, plain, ![X21]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X21)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 1.93/2.16  fof(c_0_36, plain, ![X56, X57, X58, X59]:(~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X58)))|m1_subset_1(k5_relset_1(X56,X58,X59,X57),k1_zfmisc_1(k2_zfmisc_1(X57,X58)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_relset_1])])).
% 1.93/2.16  cnf(c_0_37, plain, (k5_relset_1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.93/2.16  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.93/2.16  fof(c_0_39, plain, ![X19, X20]:((k2_zfmisc_1(X19,X20)!=k1_xboole_0|(X19=k1_xboole_0|X20=k1_xboole_0))&((X19!=k1_xboole_0|k2_zfmisc_1(X19,X20)=k1_xboole_0)&(X20!=k1_xboole_0|k2_zfmisc_1(X19,X20)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.93/2.16  cnf(c_0_40, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.93/2.16  cnf(c_0_41, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.93/2.16  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.93/2.16  cnf(c_0_43, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.93/2.16  cnf(c_0_44, plain, (m1_subset_1(k5_relset_1(X2,X3,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.93/2.16  cnf(c_0_45, plain, (k5_relset_1(X1,X2,k2_zfmisc_1(X1,X2),X3)=k7_relat_1(k2_zfmisc_1(X1,X2),X3)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.93/2.16  cnf(c_0_46, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.93/2.16  fof(c_0_47, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.93/2.16  fof(c_0_48, plain, ![X17, X18]:(~v1_xboole_0(X17)|X17=X18|~v1_xboole_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 1.93/2.16  cnf(c_0_49, plain, (v1_xboole_0(X1)|~r1_tarski(X1,esk1_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.93/2.16  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.93/2.16  fof(c_0_51, plain, ![X22, X23]:(~v1_xboole_0(X22)|(~m1_subset_1(X23,k1_zfmisc_1(X22))|v1_xboole_0(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 1.93/2.16  cnf(c_0_52, plain, (m1_subset_1(k7_relat_1(k2_zfmisc_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_38]), c_0_45])).
% 1.93/2.16  cnf(c_0_53, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_46])).
% 1.93/2.16  fof(c_0_54, plain, ![X46, X47, X48]:((v4_relat_1(X48,X46)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(v5_relat_1(X48,X47)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 1.93/2.16  fof(c_0_55, plain, ![X43, X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|v1_relat_1(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.93/2.16  fof(c_0_56, plain, ![X29, X30, X31]:(~v1_relat_1(X31)|(~r1_tarski(X29,X30)|k7_relat_1(k7_relat_1(X31,X30),X29)=k7_relat_1(X31,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).
% 1.93/2.16  cnf(c_0_57, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.93/2.16  cnf(c_0_58, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.93/2.16  cnf(c_0_59, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.93/2.16  cnf(c_0_60, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.93/2.16  cnf(c_0_61, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.93/2.16  cnf(c_0_62, plain, (m1_subset_1(k7_relat_1(k2_zfmisc_1(X1,X2),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.93/2.16  fof(c_0_63, plain, ![X32, X33]:(~v1_relat_1(X33)|~v4_relat_1(X33,X32)|X33=k7_relat_1(X33,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 1.93/2.16  cnf(c_0_64, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.93/2.16  cnf(c_0_65, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.93/2.16  cnf(c_0_66, plain, (k7_relat_1(k7_relat_1(X1,X3),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.93/2.16  cnf(c_0_67, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 1.93/2.16  cnf(c_0_68, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 1.93/2.16  cnf(c_0_69, plain, (v1_xboole_0(k7_relat_1(k2_zfmisc_1(X1,X2),k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_60])])).
% 1.93/2.16  cnf(c_0_70, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.93/2.16  cnf(c_0_71, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_43])).
% 1.93/2.16  cnf(c_0_72, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_43])).
% 1.93/2.16  fof(c_0_73, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:((~(v2_struct_0(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((v1_funct_1(k5_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4))&v1_funct_2(k5_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),u1_struct_0(k1_pre_topc(X1,X4)),u1_struct_0(X2)))&m1_subset_1(k5_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X4)),u1_struct_0(X2)))))))))), inference(assume_negation,[status(cth)],[t30_pre_topc])).
% 1.93/2.16  cnf(c_0_74, plain, (v4_relat_1(k2_zfmisc_1(X1,X2),X1)), inference(spm,[status(thm)],[c_0_64, c_0_38])).
% 1.93/2.16  cnf(c_0_75, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_65, c_0_38])).
% 1.93/2.16  cnf(c_0_76, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,X3)|~v1_relat_1(X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 1.93/2.16  cnf(c_0_77, plain, (k7_relat_1(k2_zfmisc_1(X1,X2),k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 1.93/2.16  cnf(c_0_78, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])])).
% 1.93/2.16  fof(c_0_79, plain, ![X77, X78]:(~l1_pre_topc(X77)|(~m1_subset_1(X78,k1_zfmisc_1(u1_struct_0(X77)))|u1_struct_0(k1_pre_topc(X77,X78))=X78)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 1.93/2.16  fof(c_0_80, negated_conjecture, (l1_pre_topc(esk3_0)&((~v2_struct_0(esk4_0)&l1_pre_topc(esk4_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(~v1_funct_1(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))|~v1_funct_2(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0),u1_struct_0(k1_pre_topc(esk3_0,esk6_0)),u1_struct_0(esk4_0))|~m1_subset_1(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(esk3_0,esk6_0)),u1_struct_0(esk4_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_73])])])])).
% 1.93/2.16  fof(c_0_81, plain, ![X36, X37]:(~v1_relat_1(X37)|(~r1_tarski(X36,k1_relat_1(X37))|k1_relat_1(k7_relat_1(X37,X36))=X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 1.93/2.16  fof(c_0_82, plain, ![X60, X61, X62]:(((v1_funct_1(X62)|(~v1_funct_1(X62)|~v1_funct_2(X62,X60,X61))|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|(v1_xboole_0(X60)|v1_xboole_0(X61)))&(~v1_xboole_0(X62)|(~v1_funct_1(X62)|~v1_funct_2(X62,X60,X61))|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|(v1_xboole_0(X60)|v1_xboole_0(X61))))&(v1_funct_2(X62,X60,X61)|(~v1_funct_1(X62)|~v1_funct_2(X62,X60,X61))|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|(v1_xboole_0(X60)|v1_xboole_0(X61)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).
% 1.93/2.16  fof(c_0_83, plain, ![X38]:(~v1_xboole_0(X38)|v1_funct_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 1.93/2.16  fof(c_0_84, plain, ![X49, X50, X51]:(~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|k1_relset_1(X49,X50,X51)=k1_relat_1(X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 1.93/2.16  cnf(c_0_85, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.93/2.16  cnf(c_0_86, plain, (k7_relat_1(k2_zfmisc_1(X1,X2),X1)=k2_zfmisc_1(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_74]), c_0_75])])).
% 1.93/2.16  cnf(c_0_87, plain, (k7_relat_1(k2_zfmisc_1(X1,X2),X3)=k1_xboole_0|~v1_xboole_0(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_75])])).
% 1.93/2.16  cnf(c_0_88, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 1.93/2.16  cnf(c_0_89, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.93/2.16  cnf(c_0_90, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.93/2.16  fof(c_0_91, plain, ![X39, X40]:((v1_relat_1(k7_relat_1(X39,X40))|(~v1_relat_1(X39)|~v1_funct_1(X39)))&(v1_funct_1(k7_relat_1(X39,X40))|(~v1_relat_1(X39)|~v1_funct_1(X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 1.93/2.16  cnf(c_0_92, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.93/2.16  cnf(c_0_93, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 1.93/2.16  cnf(c_0_94, plain, (v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 1.93/2.16  cnf(c_0_95, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 1.93/2.16  fof(c_0_96, plain, ![X74, X75, X76]:(((v1_funct_1(X76)|k1_relset_1(X74,X75,X76)!=X74|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75)))))&(v1_funct_2(X76,X74,X75)|k1_relset_1(X74,X75,X76)!=X74|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75))))))&(m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75)))|k1_relset_1(X74,X75,X76)!=X74|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_funct_2])])])).
% 1.93/2.16  cnf(c_0_97, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 1.93/2.16  cnf(c_0_98, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_85])).
% 1.93/2.16  cnf(c_0_99, plain, (k1_xboole_0=k2_zfmisc_1(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 1.93/2.16  cnf(c_0_100, negated_conjecture, (~v1_funct_1(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))|~v1_funct_2(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0),u1_struct_0(k1_pre_topc(esk3_0,esk6_0)),u1_struct_0(esk4_0))|~m1_subset_1(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(esk3_0,esk6_0)),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.93/2.16  cnf(c_0_101, negated_conjecture, (u1_struct_0(k1_pre_topc(esk3_0,esk6_0))=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])])).
% 1.93/2.16  cnf(c_0_102, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 1.93/2.16  cnf(c_0_103, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_65, c_0_92])).
% 1.93/2.16  cnf(c_0_104, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.93/2.16  cnf(c_0_105, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_93, c_0_67])).
% 1.93/2.16  cnf(c_0_106, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X3)), inference(csr,[status(thm)],[c_0_94, c_0_95])).
% 1.93/2.16  cnf(c_0_107, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_31, c_0_67])).
% 1.93/2.16  cnf(c_0_108, plain, (v1_funct_2(X1,X2,X3)|k1_relset_1(X2,X3,X1)!=X2|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 1.93/2.16  cnf(c_0_109, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_97, c_0_43])).
% 1.93/2.16  cnf(c_0_110, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_95, c_0_60])).
% 1.93/2.16  fof(c_0_111, plain, ![X34, X35]:(~v1_relat_1(X35)|r1_tarski(k7_relat_1(X35,X34),X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 1.93/2.16  cnf(c_0_112, plain, (k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))=k2_zfmisc_1(X2,X3)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 1.93/2.16  cnf(c_0_113, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_60, c_0_99])).
% 1.93/2.16  cnf(c_0_114, negated_conjecture, (~v1_funct_2(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0),esk6_0,u1_struct_0(esk4_0))|~v1_funct_1(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))|~m1_subset_1(k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,u1_struct_0(esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_101]), c_0_101])).
% 1.93/2.16  cnf(c_0_115, negated_conjecture, (k5_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)=k7_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_37, c_0_92])).
% 1.93/2.16  cnf(c_0_116, negated_conjecture, (v1_funct_1(k7_relat_1(esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104])])).
% 1.93/2.16  cnf(c_0_117, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_86]), c_0_75])])).
% 1.93/2.16  cnf(c_0_118, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_funct_2(X3,X2,X1)|~v1_xboole_0(X3)), inference(csr,[status(thm)],[c_0_106, c_0_107])).
% 1.93/2.16  cnf(c_0_119, plain, (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_110]), c_0_43])])])).
% 1.93/2.16  cnf(c_0_120, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_111])).
% 1.93/2.16  cnf(c_0_121, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_65, c_0_107])).
% 1.93/2.16  cnf(c_0_122, plain, (k2_zfmisc_1(X1,X2)=X2|~v1_xboole_0(X3)|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_59]), c_0_113])).
% 1.93/2.16  cnf(c_0_123, negated_conjecture, (~v1_funct_2(k7_relat_1(esk5_0,esk6_0),esk6_0,u1_struct_0(esk4_0))|~m1_subset_1(k7_relat_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_115]), c_0_115]), c_0_116]), c_0_115])])).
% 1.93/2.16  cnf(c_0_124, negated_conjecture, (m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk4_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_92]), c_0_115])).
% 1.93/2.16  cnf(c_0_125, plain, (k1_relat_1(X1)=X2|~v1_xboole_0(k2_zfmisc_1(X2,X3))|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_117, c_0_59])).
% 1.93/2.16  cnf(c_0_126, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))|v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_60])])).
% 1.93/2.16  cnf(c_0_127, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 1.93/2.16  cnf(c_0_128, plain, (v1_xboole_0(k7_relat_1(k2_zfmisc_1(X1,X2),X3))|~v1_xboole_0(k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_61, c_0_52])).
% 1.93/2.16  cnf(c_0_129, plain, (k2_zfmisc_1(X1,X2)=X2|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_122, c_0_60])).
% 1.93/2.16  fof(c_0_130, plain, ![X66, X67, X68, X69]:((v1_funct_1(k2_partfun1(X66,X67,X68,X69))|(~v1_funct_1(X68)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))))&(m1_subset_1(k2_partfun1(X66,X67,X68,X69),k1_zfmisc_1(k2_zfmisc_1(X66,X67)))|(~v1_funct_1(X68)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 1.93/2.16  fof(c_0_131, plain, ![X70, X71, X72, X73]:(~v1_funct_1(X72)|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))|k2_partfun1(X70,X71,X72,X73)=k7_relat_1(X72,X73)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 1.93/2.16  cnf(c_0_132, negated_conjecture, (~v1_funct_2(k7_relat_1(esk5_0,esk6_0),esk6_0,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_124])])).
% 1.93/2.16  cnf(c_0_133, plain, (k1_relat_1(X1)=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_98]), c_0_60])])).
% 1.93/2.16  cnf(c_0_134, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(ef,[status(thm)],[c_0_126])).
% 1.93/2.16  cnf(c_0_135, plain, (m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_31, c_0_127])).
% 1.93/2.16  cnf(c_0_136, plain, (v1_xboole_0(k7_relat_1(k2_zfmisc_1(X1,X2),X3))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_128, c_0_129])).
% 1.93/2.16  cnf(c_0_137, plain, (m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_130])).
% 1.93/2.16  cnf(c_0_138, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_131])).
% 1.93/2.16  cnf(c_0_139, negated_conjecture, (~v1_funct_2(k7_relat_1(esk5_0,esk6_0),esk6_0,k1_relat_1(X1))|~v1_xboole_0(u1_struct_0(esk4_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_132, c_0_133])).
% 1.93/2.16  cnf(c_0_140, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_134])).
% 1.93/2.16  cnf(c_0_141, plain, (v1_xboole_0(k7_relat_1(X1,X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_61, c_0_135])).
% 1.93/2.16  cnf(c_0_142, negated_conjecture, (v1_xboole_0(esk5_0)|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_61, c_0_92])).
% 1.93/2.16  cnf(c_0_143, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_136, c_0_86])).
% 1.93/2.16  cnf(c_0_144, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_42, c_0_92])).
% 1.93/2.16  cnf(c_0_145, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.93/2.16  cnf(c_0_146, negated_conjecture, (m1_subset_1(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_92]), c_0_104])])).
% 1.93/2.16  cnf(c_0_147, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)=k7_relat_1(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_92]), c_0_104])])).
% 1.93/2.16  cnf(c_0_148, negated_conjecture, (v1_xboole_0(k7_relat_1(esk5_0,X1))|~v1_xboole_0(k2_zfmisc_1(X1,u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_61, c_0_124])).
% 1.93/2.16  cnf(c_0_149, negated_conjecture, (~v1_funct_2(k7_relat_1(esk5_0,esk6_0),esk6_0,k1_xboole_0)|~v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_60])])).
% 1.93/2.16  cnf(c_0_150, plain, (k7_relat_1(X1,X2)=X3|~v1_xboole_0(X3)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_59, c_0_141])).
% 1.93/2.16  cnf(c_0_151, negated_conjecture, (v1_xboole_0(esk5_0)|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_142, c_0_143])).
% 1.93/2.16  cnf(c_0_152, negated_conjecture, (k7_relat_1(k7_relat_1(X1,k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))),esk5_0)=k7_relat_1(X1,esk5_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_144])).
% 1.93/2.16  cnf(c_0_153, plain, (k1_xboole_0=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_99, c_0_143])).
% 1.93/2.16  cnf(c_0_154, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_145, c_0_67])).
% 1.93/2.16  cnf(c_0_155, negated_conjecture, (r1_tarski(k7_relat_1(esk5_0,X1),k2_zfmisc_1(X1,u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_42, c_0_124])).
% 1.93/2.16  cnf(c_0_156, negated_conjecture, (k1_relat_1(esk5_0)=k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_97, c_0_92])).
% 1.93/2.16  cnf(c_0_157, negated_conjecture, (m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_146, c_0_147])).
% 1.93/2.16  fof(c_0_158, plain, ![X63, X64, X65]:((((~v1_funct_2(X65,X63,X64)|X63=k1_relset_1(X63,X64,X65)|X64=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))&(X63!=k1_relset_1(X63,X64,X65)|v1_funct_2(X65,X63,X64)|X64=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))))&((~v1_funct_2(X65,X63,X64)|X63=k1_relset_1(X63,X64,X65)|X63!=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))&(X63!=k1_relset_1(X63,X64,X65)|v1_funct_2(X65,X63,X64)|X63!=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))))&((~v1_funct_2(X65,X63,X64)|X65=k1_xboole_0|X63=k1_xboole_0|X64!=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))&(X65!=k1_xboole_0|v1_funct_2(X65,X63,X64)|X63=k1_xboole_0|X64!=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 1.93/2.16  cnf(c_0_159, negated_conjecture, (v1_xboole_0(k7_relat_1(esk5_0,X1))|~v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(u1_struct_0(esk4_0))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_148, c_0_59])).
% 1.93/2.16  cnf(c_0_160, negated_conjecture, (~v1_funct_2(k7_relat_1(k7_relat_1(X1,X2),esk6_0),esk6_0,k1_xboole_0)|~v1_xboole_0(u1_struct_0(esk4_0))|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_150]), c_0_151])).
% 1.93/2.16  cnf(c_0_161, negated_conjecture, (k7_relat_1(k7_relat_1(esk5_0,k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))),esk5_0)=k7_relat_1(esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_152, c_0_103])).
% 1.93/2.16  cnf(c_0_162, negated_conjecture, (v1_xboole_0(k7_relat_1(esk5_0,k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_153]), c_0_60])])).
% 1.93/2.16  cnf(c_0_163, negated_conjecture, (k7_relat_1(esk5_0,X1)=k2_zfmisc_1(X1,u1_struct_0(esk4_0))|~v1_xboole_0(k2_zfmisc_1(X1,u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_154, c_0_155])).
% 1.93/2.16  cnf(c_0_164, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_64, c_0_98])).
% 1.93/2.16  cnf(c_0_165, plain, (m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(X3))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_107, c_0_141])).
% 1.93/2.16  cnf(c_0_166, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_xboole_0(k2_zfmisc_1(X3,X4))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_75, c_0_150])).
% 1.93/2.16  cnf(c_0_167, negated_conjecture, (r1_tarski(esk6_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_89])).
% 1.93/2.16  cnf(c_0_168, negated_conjecture, (k1_relat_1(k7_relat_1(esk5_0,X1))=X1|~r1_tarski(X1,k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_156]), c_0_103])])).
% 1.93/2.16  cnf(c_0_169, negated_conjecture, (k1_relat_1(k7_relat_1(esk5_0,X1))=k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k7_relat_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_97, c_0_157])).
% 1.93/2.16  cnf(c_0_170, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_158])).
% 1.93/2.16  cnf(c_0_171, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.93/2.16  cnf(c_0_172, negated_conjecture, (~v1_funct_2(k7_relat_1(X1,X2),esk6_0,u1_struct_0(esk4_0))|~v1_xboole_0(k7_relat_1(esk5_0,esk6_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_132, c_0_150])).
% 1.93/2.16  cnf(c_0_173, negated_conjecture, (v1_xboole_0(k7_relat_1(esk5_0,X1))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_98]), c_0_60])])).
% 1.93/2.16  cnf(c_0_174, negated_conjecture, (~v1_funct_2(k7_relat_1(k7_relat_1(esk5_0,esk5_0),esk6_0),esk6_0,k1_xboole_0)|~v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_161]), c_0_162])).
% 1.93/2.16  cnf(c_0_175, negated_conjecture, (k7_relat_1(esk5_0,X1)=k2_zfmisc_1(X1,u1_struct_0(esk4_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_163, c_0_113])).
% 1.93/2.16  cnf(c_0_176, plain, (v4_relat_1(k7_relat_1(X1,X2),X3)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_164, c_0_165])).
% 1.93/2.16  cnf(c_0_177, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166, c_0_53]), c_0_60])])).
% 1.93/2.16  cnf(c_0_178, negated_conjecture, (k7_relat_1(k7_relat_1(X1,u1_struct_0(esk3_0)),esk6_0)=k7_relat_1(X1,esk6_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_167])).
% 1.93/2.16  cnf(c_0_179, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k7_relat_1(esk5_0,X1))=X1|~r1_tarski(X1,k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))), inference(rw,[status(thm)],[c_0_168, c_0_169])).
% 1.93/2.16  cnf(c_0_180, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=u1_struct_0(esk3_0)|u1_struct_0(esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_171]), c_0_92])])).
% 1.93/2.16  cnf(c_0_181, negated_conjecture, (~v1_funct_2(k7_relat_1(X1,X2),esk6_0,k7_relat_1(X3,X4))|~v1_xboole_0(u1_struct_0(esk4_0))|~v1_xboole_0(X1)|~v1_xboole_0(X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_172, c_0_150]), c_0_173])).
% 1.93/2.16  cnf(c_0_182, negated_conjecture, (~v1_funct_2(k7_relat_1(k2_zfmisc_1(esk5_0,u1_struct_0(esk4_0)),esk6_0),esk6_0,k1_xboole_0)|~v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_175]), c_0_151])).
% 1.93/2.16  cnf(c_0_183, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,X2)|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_176]), c_0_177])).
% 1.93/2.16  cnf(c_0_184, negated_conjecture, (k7_relat_1(k7_relat_1(X1,u1_struct_0(esk3_0)),esk6_0)=k7_relat_1(X1,esk6_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_178, c_0_121])).
% 1.93/2.16  cnf(c_0_185, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k7_relat_1(esk5_0,X1))=k1_relset_1(X1,u1_struct_0(esk4_0),k7_relat_1(esk5_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_124]), c_0_169])).
% 1.93/2.16  cnf(c_0_186, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k7_relat_1(esk5_0,X1))=X1|u1_struct_0(esk4_0)=k1_xboole_0|~r1_tarski(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_179, c_0_180])).
% 1.93/2.16  cnf(c_0_187, negated_conjecture, (~v1_funct_2(k7_relat_1(X1,X2),esk6_0,k1_xboole_0)|~v1_xboole_0(u1_struct_0(esk4_0))|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_78]), c_0_60])])).
% 1.93/2.16  cnf(c_0_188, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_158])).
% 1.93/2.16  cnf(c_0_189, negated_conjecture, (~v1_funct_2(k7_relat_1(u1_struct_0(esk4_0),esk6_0),esk6_0,k1_xboole_0)|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_182, c_0_129])).
% 1.93/2.16  cnf(c_0_190, negated_conjecture, (k7_relat_1(X1,esk6_0)=k7_relat_1(X1,u1_struct_0(esk3_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_183, c_0_184])).
% 1.93/2.16  cnf(c_0_191, negated_conjecture, (v1_funct_2(k7_relat_1(esk5_0,X1),X1,u1_struct_0(esk4_0))|k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k7_relat_1(esk5_0,X1))!=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_185]), c_0_116]), c_0_124])])).
% 1.93/2.16  cnf(c_0_192, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),k7_relat_1(esk5_0,esk6_0))=esk6_0|u1_struct_0(esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_186, c_0_167])).
% 1.93/2.16  cnf(c_0_193, negated_conjecture, (~v1_funct_2(k1_xboole_0,esk6_0,k1_xboole_0)|~v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187, c_0_78]), c_0_60])])).
% 1.93/2.16  cnf(c_0_194, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_188])]), c_0_98]), c_0_43])])).
% 1.93/2.16  cnf(c_0_195, negated_conjecture, (~v1_funct_2(k7_relat_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)),esk6_0,k1_xboole_0)|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_189, c_0_190])).
% 1.93/2.16  cnf(c_0_196, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_191, c_0_192]), c_0_132])).
% 1.93/2.16  cnf(c_0_197, negated_conjecture, (esk6_0=k1_xboole_0|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_193, c_0_194])).
% 1.93/2.16  cnf(c_0_198, negated_conjecture, (~v1_funct_2(k1_xboole_0,esk6_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_195, c_0_196]), c_0_78]), c_0_196]), c_0_60])])).
% 1.93/2.16  cnf(c_0_199, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_197, c_0_196]), c_0_60])])).
% 1.93/2.16  cnf(c_0_200, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(rw,[status(thm)],[c_0_119, c_0_140])).
% 1.93/2.16  cnf(c_0_201, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_198, c_0_199]), c_0_200])]), ['proof']).
% 1.93/2.16  # SZS output end CNFRefutation
% 1.93/2.16  # Proof object total steps             : 202
% 1.93/2.16  # Proof object clause steps            : 147
% 1.93/2.16  # Proof object formula steps           : 55
% 1.93/2.16  # Proof object conjectures             : 61
% 1.93/2.16  # Proof object clause conjectures      : 58
% 1.93/2.16  # Proof object formula conjectures     : 3
% 1.93/2.16  # Proof object initial clauses used    : 37
% 1.93/2.16  # Proof object initial formulas used   : 27
% 1.93/2.16  # Proof object generating inferences   : 95
% 1.93/2.16  # Proof object simplifying inferences  : 89
% 1.93/2.16  # Training examples: 0 positive, 0 negative
% 1.93/2.16  # Parsed axioms                        : 28
% 1.93/2.16  # Removed by relevancy pruning/SinE    : 0
% 1.93/2.16  # Initial clauses                      : 55
% 1.93/2.16  # Removed in clause preprocessing      : 4
% 1.93/2.16  # Initial clauses in saturation        : 51
% 1.93/2.16  # Processed clauses                    : 30862
% 1.93/2.16  # ...of these trivial                  : 28
% 1.93/2.16  # ...subsumed                          : 27338
% 1.93/2.16  # ...remaining for further processing  : 3496
% 1.93/2.16  # Other redundant clauses eliminated   : 112
% 1.93/2.16  # Clauses deleted for lack of memory   : 0
% 1.93/2.16  # Backward-subsumed                    : 634
% 1.93/2.16  # Backward-rewritten                   : 2016
% 1.93/2.16  # Generated clauses                    : 161932
% 1.93/2.16  # ...of the previous two non-trivial   : 146883
% 1.93/2.16  # Contextual simplify-reflections      : 175
% 1.93/2.16  # Paramodulations                      : 161819
% 1.93/2.16  # Factorizations                       : 2
% 1.93/2.16  # Equation resolutions                 : 112
% 1.93/2.16  # Propositional unsat checks           : 0
% 1.93/2.16  #    Propositional check models        : 0
% 1.93/2.16  #    Propositional check unsatisfiable : 0
% 1.93/2.16  #    Propositional clauses             : 0
% 1.93/2.16  #    Propositional clauses after purity: 0
% 1.93/2.16  #    Propositional unsat core size     : 0
% 1.93/2.16  #    Propositional preprocessing time  : 0.000
% 1.93/2.16  #    Propositional encoding time       : 0.000
% 1.93/2.16  #    Propositional solver time         : 0.000
% 1.93/2.16  #    Success case prop preproc time    : 0.000
% 1.93/2.16  #    Success case prop encoding time   : 0.000
% 1.93/2.16  #    Success case prop solver time     : 0.000
% 1.93/2.16  # Current number of processed clauses  : 788
% 1.93/2.16  #    Positive orientable unit clauses  : 44
% 1.93/2.16  #    Positive unorientable unit clauses: 0
% 1.93/2.16  #    Negative unit clauses             : 2
% 1.93/2.16  #    Non-unit-clauses                  : 742
% 1.93/2.16  # Current number of unprocessed clauses: 113459
% 1.93/2.16  # ...number of literals in the above   : 526379
% 1.93/2.16  # Current number of archived formulas  : 0
% 1.93/2.16  # Current number of archived clauses   : 2700
% 1.93/2.16  # Clause-clause subsumption calls (NU) : 2343081
% 1.93/2.16  # Rec. Clause-clause subsumption calls : 868598
% 1.93/2.16  # Non-unit clause-clause subsumptions  : 24712
% 1.93/2.16  # Unit Clause-clause subsumption calls : 6173
% 1.93/2.16  # Rewrite failures with RHS unbound    : 2
% 1.93/2.16  # BW rewrite match attempts            : 195
% 1.93/2.16  # BW rewrite match successes           : 23
% 1.93/2.16  # Condensation attempts                : 0
% 1.93/2.16  # Condensation successes               : 0
% 1.93/2.16  # Termbank termtop insertions          : 2300577
% 1.93/2.16  
% 1.93/2.16  # -------------------------------------------------
% 1.93/2.16  # User time                : 1.741 s
% 1.93/2.16  # System time              : 0.051 s
% 1.93/2.16  # Total time               : 1.792 s
% 1.93/2.16  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
