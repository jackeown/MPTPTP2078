%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 (1802 expanded)
%              Number of clauses        :   69 ( 653 expanded)
%              Number of leaves         :   25 ( 453 expanded)
%              Depth                    :   14
%              Number of atoms          :  440 (10858 expanded)
%              Number of equality atoms :   68 ( 673 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(dt_k1_yellow_1,axiom,(
    ! [X1] :
      ( v1_relat_2(k1_yellow_1(X1))
      & v4_relat_2(k1_yellow_1(X1))
      & v8_relat_2(k1_yellow_1(X1))
      & v1_partfun1(k1_yellow_1(X1),X1)
      & m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(t68_tex_2,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => v5_pre_topc(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t17_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t18_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(t56_tops_2,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v5_pre_topc(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_2)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(c_0_25,plain,(
    ! [X15,X16] :
      ( ( k2_zfmisc_1(X15,X16) != k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_26,plain,(
    ! [X60] :
      ( v1_relat_2(k1_yellow_1(X60))
      & v4_relat_2(k1_yellow_1(X60))
      & v8_relat_2(k1_yellow_1(X60))
      & v1_partfun1(k1_yellow_1(X60),X60)
      & m1_subset_1(k1_yellow_1(X60),k1_zfmisc_1(k2_zfmisc_1(X60,X60))) ) ),
    inference(variable_rename,[status(thm)],[dt_k1_yellow_1])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => v5_pre_topc(X3,X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t68_tex_2])).

fof(c_0_29,plain,(
    ! [X25,X26,X27] :
      ( ~ r2_hidden(X25,X26)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X27))
      | ~ v1_xboole_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_30,plain,
    ( m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X62,X63] :
      ( ( ~ v1_tdlat_3(X62)
        | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))
        | v3_pre_topc(X63,X62)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62) )
      & ( m1_subset_1(esk4_1(X62),k1_zfmisc_1(u1_struct_0(X62)))
        | v1_tdlat_3(X62)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62) )
      & ( ~ v3_pre_topc(esk4_1(X62),X62)
        | v1_tdlat_3(X62)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).

fof(c_0_33,plain,(
    ! [X61] :
      ( ~ l1_pre_topc(X61)
      | ~ v1_tdlat_3(X61)
      | v2_pre_topc(X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

fof(c_0_34,plain,(
    ! [X34,X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | m1_subset_1(k8_relset_1(X34,X35,X36,X37),k1_zfmisc_1(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

fof(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk6_0)
    & v1_tdlat_3(esk6_0)
    & l1_pre_topc(esk6_0)
    & v2_pre_topc(esk7_0)
    & l1_pre_topc(esk7_0)
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))))
    & ~ v5_pre_topc(esk8_0,esk6_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_yellow_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_39,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_40,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k1_yellow_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_47,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_48,plain,(
    ! [X46] :
      ( ~ l1_struct_0(X46)
      | k2_struct_0(X46) = u1_struct_0(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_49,plain,(
    ! [X47] :
      ( ~ l1_pre_topc(X47)
      | l1_struct_0(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_50,plain,(
    ! [X50,X51,X52,X53] :
      ( ( ~ v5_pre_topc(X52,X50,X51)
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))
        | ~ v3_pre_topc(X53,X51)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X50),u1_struct_0(X51),X52,X53),X50)
        | k2_struct_0(X51) = k1_xboole_0
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51))))
        | ~ l1_pre_topc(X51)
        | ~ l1_pre_topc(X50) )
      & ( m1_subset_1(esk2_3(X50,X51,X52),k1_zfmisc_1(u1_struct_0(X51)))
        | v5_pre_topc(X52,X50,X51)
        | k2_struct_0(X51) = k1_xboole_0
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51))))
        | ~ l1_pre_topc(X51)
        | ~ l1_pre_topc(X50) )
      & ( v3_pre_topc(esk2_3(X50,X51,X52),X51)
        | v5_pre_topc(X52,X50,X51)
        | k2_struct_0(X51) = k1_xboole_0
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51))))
        | ~ l1_pre_topc(X51)
        | ~ l1_pre_topc(X50) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X50),u1_struct_0(X51),X52,esk2_3(X50,X51,X52)),X50)
        | v5_pre_topc(X52,X50,X51)
        | k2_struct_0(X51) = k1_xboole_0
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51))))
        | ~ l1_pre_topc(X51)
        | ~ l1_pre_topc(X50) )
      & ( ~ v5_pre_topc(X52,X50,X51)
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))
        | ~ v3_pre_topc(X53,X51)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X50),u1_struct_0(X51),X52,X53),X50)
        | k2_struct_0(X50) != k1_xboole_0
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51))))
        | ~ l1_pre_topc(X51)
        | ~ l1_pre_topc(X50) )
      & ( m1_subset_1(esk2_3(X50,X51,X52),k1_zfmisc_1(u1_struct_0(X51)))
        | v5_pre_topc(X52,X50,X51)
        | k2_struct_0(X50) != k1_xboole_0
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51))))
        | ~ l1_pre_topc(X51)
        | ~ l1_pre_topc(X50) )
      & ( v3_pre_topc(esk2_3(X50,X51,X52),X51)
        | v5_pre_topc(X52,X50,X51)
        | k2_struct_0(X50) != k1_xboole_0
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51))))
        | ~ l1_pre_topc(X51)
        | ~ l1_pre_topc(X50) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X50),u1_struct_0(X51),X52,esk2_3(X50,X51,X52)),X50)
        | v5_pre_topc(X52,X50,X51)
        | k2_struct_0(X50) != k1_xboole_0
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51))))
        | ~ l1_pre_topc(X51)
        | ~ l1_pre_topc(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).

cnf(c_0_51,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k8_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0),esk8_0,X1),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( v1_tdlat_3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( v1_xboole_0(k1_yellow_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_57,plain,(
    ! [X31,X32,X33] :
      ( ( v4_relat_1(X33,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v5_relat_1(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_58,plain,(
    ! [X19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X19)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_59,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | v1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_60,plain,(
    ! [X65,X66] :
      ( ( ~ v1_tdlat_3(X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))
        | v4_pre_topc(X66,X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65) )
      & ( m1_subset_1(esk5_1(X65),k1_zfmisc_1(u1_struct_0(X65)))
        | v1_tdlat_3(X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65) )
      & ( ~ v4_pre_topc(esk5_1(X65),X65)
        | v1_tdlat_3(X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tdlat_3])])])])])).

fof(c_0_61,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_63,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_64,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_65,plain,
    ( v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_68,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_69,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_70,negated_conjecture,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0),esk8_0,X1),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])])).

fof(c_0_71,plain,(
    ! [X44,X45] :
      ( ( ~ v1_partfun1(X45,X44)
        | k1_relat_1(X45) = X44
        | ~ v1_relat_1(X45)
        | ~ v4_relat_1(X45,X44) )
      & ( k1_relat_1(X45) != X44
        | v1_partfun1(X45,X44)
        | ~ v1_relat_1(X45)
        | ~ v4_relat_1(X45,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_72,plain,
    ( v1_partfun1(k1_yellow_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_73,plain,
    ( k1_yellow_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_74,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_75,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_76,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_77,plain,(
    ! [X55,X56,X57,X58] :
      ( ( ~ v5_pre_topc(X57,X55,X56)
        | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X56)))
        | r1_tarski(k2_pre_topc(X55,k8_relset_1(u1_struct_0(X55),u1_struct_0(X56),X57,X58)),k8_relset_1(u1_struct_0(X55),u1_struct_0(X56),X57,k2_pre_topc(X56,X58)))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(X55),u1_struct_0(X56))
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X55),u1_struct_0(X56))))
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56)
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55) )
      & ( m1_subset_1(esk3_3(X55,X56,X57),k1_zfmisc_1(u1_struct_0(X56)))
        | v5_pre_topc(X57,X55,X56)
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(X55),u1_struct_0(X56))
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X55),u1_struct_0(X56))))
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56)
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55) )
      & ( ~ r1_tarski(k2_pre_topc(X55,k8_relset_1(u1_struct_0(X55),u1_struct_0(X56),X57,esk3_3(X55,X56,X57))),k8_relset_1(u1_struct_0(X55),u1_struct_0(X56),X57,k2_pre_topc(X56,esk3_3(X55,X56,X57))))
        | v5_pre_topc(X57,X55,X56)
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(X55),u1_struct_0(X56))
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X55),u1_struct_0(X56))))
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56)
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_2])])])])])).

cnf(c_0_78,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_79,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_43])).

cnf(c_0_81,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_82,negated_conjecture,
    ( k2_struct_0(esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68]),c_0_54]),c_0_43])]),c_0_69]),c_0_70])])).

cnf(c_0_83,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_84,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_85,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k1_relset_1(X38,X39,X40) = k1_relat_1(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_86,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_87,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_88,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_89,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_75])).

cnf(c_0_90,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_91,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_92,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_93,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_78,c_0_41])).

cnf(c_0_94,negated_conjecture,
    ( k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)) = esk8_0
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_95,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_68])])).

cnf(c_0_96,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_83])).

cnf(c_0_97,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

fof(c_0_98,plain,(
    ! [X41,X42,X43] :
      ( ( k7_relset_1(X41,X42,X43,X41) = k2_relset_1(X41,X42,X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( k8_relset_1(X41,X42,X43,X42) = k1_relset_1(X41,X42,X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

cnf(c_0_99,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_100,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_89])])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(esk3_3(esk6_0,esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_66]),c_0_67]),c_0_91]),c_0_92]),c_0_68]),c_0_54]),c_0_43])]),c_0_69])).

fof(c_0_102,plain,(
    ! [X48,X49] :
      ( ( ~ v4_pre_topc(X49,X48)
        | k2_pre_topc(X48,X49) = X49
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ l1_pre_topc(X48) )
      & ( ~ v2_pre_topc(X48)
        | k2_pre_topc(X48,X49) != X49
        | v4_pre_topc(X49,X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_103,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0),esk8_0,X1),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_52]),c_0_53]),c_0_54])])).

cnf(c_0_104,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95]),c_0_96]),c_0_95]),c_0_96]),c_0_97])])).

cnf(c_0_105,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_106,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_75]),c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(esk3_3(esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_101])).

cnf(c_0_108,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_109,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk6_0),k1_xboole_0,k1_xboole_0,X1),esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_95]),c_0_104])).

cnf(c_0_110,plain,
    ( k8_relset_1(X1,X2,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_75]),c_0_106])).

cnf(c_0_111,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_3(X1,X2,X3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk3_3(X1,X2,X3))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_112,negated_conjecture,
    ( esk3_3(esk6_0,esk7_0,esk8_0) = u1_struct_0(esk7_0)
    | ~ r1_tarski(u1_struct_0(esk7_0),esk3_3(esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_107])).

cnf(c_0_113,plain,
    ( k2_pre_topc(X1,k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_75])).

cnf(c_0_114,negated_conjecture,
    ( v4_pre_topc(k1_xboole_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(esk6_0,k8_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0),esk8_0,esk3_3(esk6_0,esk7_0,esk8_0))),k8_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0),esk8_0,k2_pre_topc(esk7_0,esk3_3(esk6_0,esk7_0,esk8_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_66]),c_0_67]),c_0_91]),c_0_92]),c_0_68]),c_0_54]),c_0_43])]),c_0_69])).

cnf(c_0_116,negated_conjecture,
    ( esk3_3(esk6_0,esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_95]),c_0_95]),c_0_97])]),c_0_104])).

cnf(c_0_117,negated_conjecture,
    ( k2_pre_topc(esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_54])])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_95]),c_0_95]),c_0_104]),c_0_104]),c_0_116]),c_0_110]),c_0_117]),c_0_104]),c_0_104]),c_0_116]),c_0_97])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.49  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.20/0.49  # and selection function SelectNewComplexAHPNS.
% 0.20/0.49  #
% 0.20/0.49  # Preprocessing time       : 0.030 s
% 0.20/0.49  # Presaturation interreduction done
% 0.20/0.49  
% 0.20/0.49  # Proof found!
% 0.20/0.49  # SZS status Theorem
% 0.20/0.49  # SZS output start CNFRefutation
% 0.20/0.49  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.49  fof(dt_k1_yellow_1, axiom, ![X1]:((((v1_relat_2(k1_yellow_1(X1))&v4_relat_2(k1_yellow_1(X1)))&v8_relat_2(k1_yellow_1(X1)))&v1_partfun1(k1_yellow_1(X1),X1))&m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_1)).
% 0.20/0.49  fof(t68_tex_2, conjecture, ![X1]:(((v2_pre_topc(X1)&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>v5_pre_topc(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_tex_2)).
% 0.20/0.49  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.49  fof(t17_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 0.20/0.49  fof(cc1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 0.20/0.49  fof(dt_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 0.20/0.49  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.49  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.49  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.49  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.49  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.49  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.49  fof(t55_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v3_pre_topc(X4,X2)=>v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_2)).
% 0.20/0.49  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.49  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.49  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.49  fof(t18_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tdlat_3)).
% 0.20/0.49  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.49  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.20/0.49  fof(t56_tops_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_2)).
% 0.20/0.49  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.49  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.49  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 0.20/0.49  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.20/0.49  fof(c_0_25, plain, ![X15, X16]:((k2_zfmisc_1(X15,X16)!=k1_xboole_0|(X15=k1_xboole_0|X16=k1_xboole_0))&((X15!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0)&(X16!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.49  fof(c_0_26, plain, ![X60]:((((v1_relat_2(k1_yellow_1(X60))&v4_relat_2(k1_yellow_1(X60)))&v8_relat_2(k1_yellow_1(X60)))&v1_partfun1(k1_yellow_1(X60),X60))&m1_subset_1(k1_yellow_1(X60),k1_zfmisc_1(k2_zfmisc_1(X60,X60)))), inference(variable_rename,[status(thm)],[dt_k1_yellow_1])).
% 0.20/0.49  cnf(c_0_27, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.49  fof(c_0_28, negated_conjecture, ~(![X1]:(((v2_pre_topc(X1)&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>v5_pre_topc(X3,X1,X2))))), inference(assume_negation,[status(cth)],[t68_tex_2])).
% 0.20/0.49  fof(c_0_29, plain, ![X25, X26, X27]:(~r2_hidden(X25,X26)|~m1_subset_1(X26,k1_zfmisc_1(X27))|~v1_xboole_0(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.49  cnf(c_0_30, plain, (m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.49  cnf(c_0_31, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_27])).
% 0.20/0.49  fof(c_0_32, plain, ![X62, X63]:((~v1_tdlat_3(X62)|(~m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))|v3_pre_topc(X63,X62))|(~v2_pre_topc(X62)|~l1_pre_topc(X62)))&((m1_subset_1(esk4_1(X62),k1_zfmisc_1(u1_struct_0(X62)))|v1_tdlat_3(X62)|(~v2_pre_topc(X62)|~l1_pre_topc(X62)))&(~v3_pre_topc(esk4_1(X62),X62)|v1_tdlat_3(X62)|(~v2_pre_topc(X62)|~l1_pre_topc(X62))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).
% 0.20/0.49  fof(c_0_33, plain, ![X61]:(~l1_pre_topc(X61)|(~v1_tdlat_3(X61)|v2_pre_topc(X61))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).
% 0.20/0.49  fof(c_0_34, plain, ![X34, X35, X36, X37]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|m1_subset_1(k8_relset_1(X34,X35,X36,X37),k1_zfmisc_1(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).
% 0.20/0.49  fof(c_0_35, negated_conjecture, (((v2_pre_topc(esk6_0)&v1_tdlat_3(esk6_0))&l1_pre_topc(esk6_0))&((v2_pre_topc(esk7_0)&l1_pre_topc(esk7_0))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)))))&~v5_pre_topc(esk8_0,esk6_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.20/0.49  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.49  cnf(c_0_37, plain, (m1_subset_1(k1_yellow_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.49  cnf(c_0_38, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.49  fof(c_0_39, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.49  cnf(c_0_40, plain, (v3_pre_topc(X2,X1)|~v1_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.49  cnf(c_0_41, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.49  cnf(c_0_42, plain, (m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.49  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.49  fof(c_0_44, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.49  cnf(c_0_45, plain, (~r2_hidden(X1,k1_yellow_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.20/0.49  cnf(c_0_46, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.49  fof(c_0_47, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.49  fof(c_0_48, plain, ![X46]:(~l1_struct_0(X46)|k2_struct_0(X46)=u1_struct_0(X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.49  fof(c_0_49, plain, ![X47]:(~l1_pre_topc(X47)|l1_struct_0(X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.49  fof(c_0_50, plain, ![X50, X51, X52, X53]:(((~v5_pre_topc(X52,X50,X51)|(~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))|(~v3_pre_topc(X53,X51)|v3_pre_topc(k8_relset_1(u1_struct_0(X50),u1_struct_0(X51),X52,X53),X50)))|k2_struct_0(X51)=k1_xboole_0|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|~l1_pre_topc(X51)|~l1_pre_topc(X50))&((m1_subset_1(esk2_3(X50,X51,X52),k1_zfmisc_1(u1_struct_0(X51)))|v5_pre_topc(X52,X50,X51)|k2_struct_0(X51)=k1_xboole_0|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|~l1_pre_topc(X51)|~l1_pre_topc(X50))&((v3_pre_topc(esk2_3(X50,X51,X52),X51)|v5_pre_topc(X52,X50,X51)|k2_struct_0(X51)=k1_xboole_0|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|~l1_pre_topc(X51)|~l1_pre_topc(X50))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X50),u1_struct_0(X51),X52,esk2_3(X50,X51,X52)),X50)|v5_pre_topc(X52,X50,X51)|k2_struct_0(X51)=k1_xboole_0|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|~l1_pre_topc(X51)|~l1_pre_topc(X50)))))&((~v5_pre_topc(X52,X50,X51)|(~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))|(~v3_pre_topc(X53,X51)|v3_pre_topc(k8_relset_1(u1_struct_0(X50),u1_struct_0(X51),X52,X53),X50)))|k2_struct_0(X50)!=k1_xboole_0|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|~l1_pre_topc(X51)|~l1_pre_topc(X50))&((m1_subset_1(esk2_3(X50,X51,X52),k1_zfmisc_1(u1_struct_0(X51)))|v5_pre_topc(X52,X50,X51)|k2_struct_0(X50)!=k1_xboole_0|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|~l1_pre_topc(X51)|~l1_pre_topc(X50))&((v3_pre_topc(esk2_3(X50,X51,X52),X51)|v5_pre_topc(X52,X50,X51)|k2_struct_0(X50)!=k1_xboole_0|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|~l1_pre_topc(X51)|~l1_pre_topc(X50))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X50),u1_struct_0(X51),X52,esk2_3(X50,X51,X52)),X50)|v5_pre_topc(X52,X50,X51)|k2_struct_0(X50)!=k1_xboole_0|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|~l1_pre_topc(X51)|~l1_pre_topc(X50)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).
% 0.20/0.49  cnf(c_0_51, plain, (v3_pre_topc(X1,X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.49  cnf(c_0_52, negated_conjecture, (m1_subset_1(k8_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0),esk8_0,X1),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.49  cnf(c_0_53, negated_conjecture, (v1_tdlat_3(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.49  cnf(c_0_54, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.49  cnf(c_0_55, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.49  cnf(c_0_56, plain, (v1_xboole_0(k1_yellow_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.49  fof(c_0_57, plain, ![X31, X32, X33]:((v4_relat_1(X33,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(v5_relat_1(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.49  fof(c_0_58, plain, ![X19]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X19)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.49  fof(c_0_59, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|v1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.49  fof(c_0_60, plain, ![X65, X66]:((~v1_tdlat_3(X65)|(~m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))|v4_pre_topc(X66,X65))|(~v2_pre_topc(X65)|~l1_pre_topc(X65)))&((m1_subset_1(esk5_1(X65),k1_zfmisc_1(u1_struct_0(X65)))|v1_tdlat_3(X65)|(~v2_pre_topc(X65)|~l1_pre_topc(X65)))&(~v4_pre_topc(esk5_1(X65),X65)|v1_tdlat_3(X65)|(~v2_pre_topc(X65)|~l1_pre_topc(X65))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tdlat_3])])])])])).
% 0.20/0.49  fof(c_0_61, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.49  cnf(c_0_62, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.49  cnf(c_0_63, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.49  cnf(c_0_64, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.49  cnf(c_0_65, plain, (v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.49  cnf(c_0_66, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.49  cnf(c_0_67, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.49  cnf(c_0_68, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.49  cnf(c_0_69, negated_conjecture, (~v5_pre_topc(esk8_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.49  cnf(c_0_70, negated_conjecture, (v3_pre_topc(k8_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0),esk8_0,X1),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])])).
% 0.20/0.49  fof(c_0_71, plain, ![X44, X45]:((~v1_partfun1(X45,X44)|k1_relat_1(X45)=X44|(~v1_relat_1(X45)|~v4_relat_1(X45,X44)))&(k1_relat_1(X45)!=X44|v1_partfun1(X45,X44)|(~v1_relat_1(X45)|~v4_relat_1(X45,X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.20/0.49  cnf(c_0_72, plain, (v1_partfun1(k1_yellow_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.49  cnf(c_0_73, plain, (k1_yellow_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.49  cnf(c_0_74, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.49  cnf(c_0_75, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.49  cnf(c_0_76, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.49  fof(c_0_77, plain, ![X55, X56, X57, X58]:((~v5_pre_topc(X57,X55,X56)|(~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X56)))|r1_tarski(k2_pre_topc(X55,k8_relset_1(u1_struct_0(X55),u1_struct_0(X56),X57,X58)),k8_relset_1(u1_struct_0(X55),u1_struct_0(X56),X57,k2_pre_topc(X56,X58))))|(~v1_funct_1(X57)|~v1_funct_2(X57,u1_struct_0(X55),u1_struct_0(X56))|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X55),u1_struct_0(X56)))))|(~v2_pre_topc(X56)|~l1_pre_topc(X56))|(~v2_pre_topc(X55)|~l1_pre_topc(X55)))&((m1_subset_1(esk3_3(X55,X56,X57),k1_zfmisc_1(u1_struct_0(X56)))|v5_pre_topc(X57,X55,X56)|(~v1_funct_1(X57)|~v1_funct_2(X57,u1_struct_0(X55),u1_struct_0(X56))|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X55),u1_struct_0(X56)))))|(~v2_pre_topc(X56)|~l1_pre_topc(X56))|(~v2_pre_topc(X55)|~l1_pre_topc(X55)))&(~r1_tarski(k2_pre_topc(X55,k8_relset_1(u1_struct_0(X55),u1_struct_0(X56),X57,esk3_3(X55,X56,X57))),k8_relset_1(u1_struct_0(X55),u1_struct_0(X56),X57,k2_pre_topc(X56,esk3_3(X55,X56,X57))))|v5_pre_topc(X57,X55,X56)|(~v1_funct_1(X57)|~v1_funct_2(X57,u1_struct_0(X55),u1_struct_0(X56))|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X55),u1_struct_0(X56)))))|(~v2_pre_topc(X56)|~l1_pre_topc(X56))|(~v2_pre_topc(X55)|~l1_pre_topc(X55))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_2])])])])])).
% 0.20/0.49  cnf(c_0_78, plain, (v4_pre_topc(X2,X1)|~v1_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.49  cnf(c_0_79, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.49  cnf(c_0_80, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_62, c_0_43])).
% 0.20/0.49  cnf(c_0_81, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.49  cnf(c_0_82, negated_conjecture, (k2_struct_0(esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68]), c_0_54]), c_0_43])]), c_0_69]), c_0_70])])).
% 0.20/0.49  cnf(c_0_83, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.49  fof(c_0_84, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.49  fof(c_0_85, plain, ![X38, X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|k1_relset_1(X38,X39,X40)=k1_relat_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.49  cnf(c_0_86, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.49  cnf(c_0_87, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.49  cnf(c_0_88, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.49  cnf(c_0_89, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_76, c_0_75])).
% 0.20/0.49  cnf(c_0_90, plain, (m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.49  cnf(c_0_91, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.49  cnf(c_0_92, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.49  cnf(c_0_93, plain, (v4_pre_topc(X1,X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_78, c_0_41])).
% 0.20/0.49  cnf(c_0_94, negated_conjecture, (k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))=esk8_0|~r1_tarski(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)),esk8_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.20/0.49  cnf(c_0_95, negated_conjecture, (u1_struct_0(esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_68])])).
% 0.20/0.49  cnf(c_0_96, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_83])).
% 0.20/0.49  cnf(c_0_97, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.20/0.49  fof(c_0_98, plain, ![X41, X42, X43]:((k7_relset_1(X41,X42,X43,X41)=k2_relset_1(X41,X42,X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))&(k8_relset_1(X41,X42,X43,X42)=k1_relset_1(X41,X42,X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.20/0.49  cnf(c_0_99, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.20/0.49  cnf(c_0_100, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), c_0_89])])).
% 0.20/0.49  cnf(c_0_101, negated_conjecture, (m1_subset_1(esk3_3(esk6_0,esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_66]), c_0_67]), c_0_91]), c_0_92]), c_0_68]), c_0_54]), c_0_43])]), c_0_69])).
% 0.20/0.49  fof(c_0_102, plain, ![X48, X49]:((~v4_pre_topc(X49,X48)|k2_pre_topc(X48,X49)=X49|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|~l1_pre_topc(X48))&(~v2_pre_topc(X48)|k2_pre_topc(X48,X49)!=X49|v4_pre_topc(X49,X48)|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|~l1_pre_topc(X48))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.20/0.49  cnf(c_0_103, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0),esk8_0,X1),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_52]), c_0_53]), c_0_54])])).
% 0.20/0.49  cnf(c_0_104, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95]), c_0_96]), c_0_95]), c_0_96]), c_0_97])])).
% 0.20/0.49  cnf(c_0_105, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.20/0.49  cnf(c_0_106, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_75]), c_0_100])).
% 0.20/0.49  cnf(c_0_107, negated_conjecture, (r1_tarski(esk3_3(esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_62, c_0_101])).
% 0.20/0.49  cnf(c_0_108, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.20/0.49  cnf(c_0_109, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk6_0),k1_xboole_0,k1_xboole_0,X1),esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_95]), c_0_104])).
% 0.20/0.49  cnf(c_0_110, plain, (k8_relset_1(X1,X2,k1_xboole_0,X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_75]), c_0_106])).
% 0.20/0.49  cnf(c_0_111, plain, (v5_pre_topc(X3,X1,X2)|~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_3(X1,X2,X3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk3_3(X1,X2,X3))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.49  cnf(c_0_112, negated_conjecture, (esk3_3(esk6_0,esk7_0,esk8_0)=u1_struct_0(esk7_0)|~r1_tarski(u1_struct_0(esk7_0),esk3_3(esk6_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_79, c_0_107])).
% 0.20/0.49  cnf(c_0_113, plain, (k2_pre_topc(X1,k1_xboole_0)=k1_xboole_0|~v4_pre_topc(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_108, c_0_75])).
% 0.20/0.49  cnf(c_0_114, negated_conjecture, (v4_pre_topc(k1_xboole_0,esk6_0)), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 0.20/0.49  cnf(c_0_115, negated_conjecture, (~r1_tarski(k2_pre_topc(esk6_0,k8_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0),esk8_0,esk3_3(esk6_0,esk7_0,esk8_0))),k8_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0),esk8_0,k2_pre_topc(esk7_0,esk3_3(esk6_0,esk7_0,esk8_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_66]), c_0_67]), c_0_91]), c_0_92]), c_0_68]), c_0_54]), c_0_43])]), c_0_69])).
% 0.20/0.49  cnf(c_0_116, negated_conjecture, (esk3_3(esk6_0,esk7_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_95]), c_0_95]), c_0_97])]), c_0_104])).
% 0.20/0.49  cnf(c_0_117, negated_conjecture, (k2_pre_topc(esk6_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_54])])).
% 0.20/0.49  cnf(c_0_118, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_95]), c_0_95]), c_0_104]), c_0_104]), c_0_116]), c_0_110]), c_0_117]), c_0_104]), c_0_104]), c_0_116]), c_0_97])]), ['proof']).
% 0.20/0.49  # SZS output end CNFRefutation
% 0.20/0.49  # Proof object total steps             : 119
% 0.20/0.49  # Proof object clause steps            : 69
% 0.20/0.49  # Proof object formula steps           : 50
% 0.20/0.49  # Proof object conjectures             : 29
% 0.20/0.49  # Proof object clause conjectures      : 26
% 0.20/0.49  # Proof object formula conjectures     : 3
% 0.20/0.49  # Proof object initial clauses used    : 36
% 0.20/0.49  # Proof object initial formulas used   : 25
% 0.20/0.49  # Proof object generating inferences   : 25
% 0.20/0.49  # Proof object simplifying inferences  : 70
% 0.20/0.49  # Training examples: 0 positive, 0 negative
% 0.20/0.49  # Parsed axioms                        : 29
% 0.20/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.49  # Initial clauses                      : 64
% 0.20/0.49  # Removed in clause preprocessing      : 1
% 0.20/0.49  # Initial clauses in saturation        : 63
% 0.20/0.49  # Processed clauses                    : 1259
% 0.20/0.49  # ...of these trivial                  : 40
% 0.20/0.49  # ...subsumed                          : 656
% 0.20/0.49  # ...remaining for further processing  : 562
% 0.20/0.49  # Other redundant clauses eliminated   : 19
% 0.20/0.49  # Clauses deleted for lack of memory   : 0
% 0.20/0.49  # Backward-subsumed                    : 18
% 0.20/0.49  # Backward-rewritten                   : 81
% 0.20/0.49  # Generated clauses                    : 3939
% 0.20/0.49  # ...of the previous two non-trivial   : 3410
% 0.20/0.49  # Contextual simplify-reflections      : 5
% 0.20/0.49  # Paramodulations                      : 3920
% 0.20/0.49  # Factorizations                       : 0
% 0.20/0.49  # Equation resolutions                 : 19
% 0.20/0.49  # Propositional unsat checks           : 0
% 0.20/0.49  #    Propositional check models        : 0
% 0.20/0.49  #    Propositional check unsatisfiable : 0
% 0.20/0.49  #    Propositional clauses             : 0
% 0.20/0.49  #    Propositional clauses after purity: 0
% 0.20/0.49  #    Propositional unsat core size     : 0
% 0.20/0.49  #    Propositional preprocessing time  : 0.000
% 0.20/0.49  #    Propositional encoding time       : 0.000
% 0.20/0.49  #    Propositional solver time         : 0.000
% 0.20/0.49  #    Success case prop preproc time    : 0.000
% 0.20/0.49  #    Success case prop encoding time   : 0.000
% 0.20/0.49  #    Success case prop solver time     : 0.000
% 0.20/0.49  # Current number of processed clauses  : 396
% 0.20/0.49  #    Positive orientable unit clauses  : 70
% 0.20/0.49  #    Positive unorientable unit clauses: 1
% 0.20/0.49  #    Negative unit clauses             : 2
% 0.20/0.49  #    Non-unit-clauses                  : 323
% 0.20/0.49  # Current number of unprocessed clauses: 2237
% 0.20/0.49  # ...number of literals in the above   : 9868
% 0.20/0.49  # Current number of archived formulas  : 0
% 0.20/0.49  # Current number of archived clauses   : 162
% 0.20/0.49  # Clause-clause subsumption calls (NU) : 36923
% 0.20/0.49  # Rec. Clause-clause subsumption calls : 11613
% 0.20/0.49  # Non-unit clause-clause subsumptions  : 524
% 0.20/0.49  # Unit Clause-clause subsumption calls : 505
% 0.20/0.49  # Rewrite failures with RHS unbound    : 0
% 0.20/0.49  # BW rewrite match attempts            : 170
% 0.20/0.49  # BW rewrite match successes           : 11
% 0.20/0.49  # Condensation attempts                : 0
% 0.20/0.49  # Condensation successes               : 0
% 0.20/0.49  # Termbank termtop insertions          : 54556
% 0.20/0.49  
% 0.20/0.49  # -------------------------------------------------
% 0.20/0.49  # User time                : 0.134 s
% 0.20/0.49  # System time              : 0.009 s
% 0.20/0.49  # Total time               : 0.143 s
% 0.20/0.49  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
