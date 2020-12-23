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
% DateTime   : Thu Dec  3 11:21:00 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 915 expanded)
%              Number of clauses        :   79 ( 352 expanded)
%              Number of leaves         :   26 ( 229 expanded)
%              Depth                    :   11
%              Number of atoms          :  462 (5140 expanded)
%              Number of equality atoms :   71 ( 299 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tex_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t17_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t18_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(c_0_26,negated_conjecture,(
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

fof(c_0_27,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_28,plain,(
    ! [X44] :
      ( v1_partfun1(k6_partfun1(X44),X44)
      & m1_subset_1(k6_partfun1(X44),k1_zfmisc_1(k2_zfmisc_1(X44,X44))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_29,plain,(
    ! [X18,X19] :
      ( ( k2_zfmisc_1(X18,X19) != k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_30,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_31,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_32,plain,(
    ! [X60,X61] :
      ( ( ~ v1_tdlat_3(X60)
        | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))
        | v3_pre_topc(X61,X60)
        | ~ v2_pre_topc(X60)
        | ~ l1_pre_topc(X60) )
      & ( m1_subset_1(esk5_1(X60),k1_zfmisc_1(u1_struct_0(X60)))
        | v1_tdlat_3(X60)
        | ~ v2_pre_topc(X60)
        | ~ l1_pre_topc(X60) )
      & ( ~ v3_pre_topc(esk5_1(X60),X60)
        | v1_tdlat_3(X60)
        | ~ v2_pre_topc(X60)
        | ~ l1_pre_topc(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).

fof(c_0_33,plain,(
    ! [X59] :
      ( ~ l1_pre_topc(X59)
      | ~ v1_tdlat_3(X59)
      | v2_pre_topc(X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

fof(c_0_34,plain,(
    ! [X32,X33,X34,X35] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | m1_subset_1(k8_relset_1(X32,X33,X34,X35),k1_zfmisc_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

fof(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk7_0)
    & v1_tdlat_3(esk7_0)
    & l1_pre_topc(esk7_0)
    & v2_pre_topc(esk8_0)
    & l1_pre_topc(esk8_0)
    & v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))))
    & ~ v5_pre_topc(esk9_0,esk7_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_39,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_42,plain,(
    ! [X21] : m1_subset_1(k2_subset_1(X21),k1_zfmisc_1(X21)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_43,plain,(
    ! [X20] : k2_subset_1(X20) = X20 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_44,plain,(
    ! [X49,X50,X51,X52] :
      ( ( ~ v5_pre_topc(X51,X49,X50)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X50)))
        | ~ v3_pre_topc(X52,X50)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51,X52),X49)
        | k2_struct_0(X50) = k1_xboole_0
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50))))
        | ~ l1_pre_topc(X50)
        | ~ l1_pre_topc(X49) )
      & ( m1_subset_1(esk3_3(X49,X50,X51),k1_zfmisc_1(u1_struct_0(X50)))
        | v5_pre_topc(X51,X49,X50)
        | k2_struct_0(X50) = k1_xboole_0
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50))))
        | ~ l1_pre_topc(X50)
        | ~ l1_pre_topc(X49) )
      & ( v3_pre_topc(esk3_3(X49,X50,X51),X50)
        | v5_pre_topc(X51,X49,X50)
        | k2_struct_0(X50) = k1_xboole_0
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50))))
        | ~ l1_pre_topc(X50)
        | ~ l1_pre_topc(X49) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51,esk3_3(X49,X50,X51)),X49)
        | v5_pre_topc(X51,X49,X50)
        | k2_struct_0(X50) = k1_xboole_0
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50))))
        | ~ l1_pre_topc(X50)
        | ~ l1_pre_topc(X49) )
      & ( ~ v5_pre_topc(X51,X49,X50)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X50)))
        | ~ v3_pre_topc(X52,X50)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51,X52),X49)
        | k2_struct_0(X49) != k1_xboole_0
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50))))
        | ~ l1_pre_topc(X50)
        | ~ l1_pre_topc(X49) )
      & ( m1_subset_1(esk3_3(X49,X50,X51),k1_zfmisc_1(u1_struct_0(X50)))
        | v5_pre_topc(X51,X49,X50)
        | k2_struct_0(X49) != k1_xboole_0
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50))))
        | ~ l1_pre_topc(X50)
        | ~ l1_pre_topc(X49) )
      & ( v3_pre_topc(esk3_3(X49,X50,X51),X50)
        | v5_pre_topc(X51,X49,X50)
        | k2_struct_0(X49) != k1_xboole_0
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50))))
        | ~ l1_pre_topc(X50)
        | ~ l1_pre_topc(X49) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51,esk3_3(X49,X50,X51)),X49)
        | v5_pre_topc(X51,X49,X50)
        | k2_struct_0(X49) != k1_xboole_0
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50))))
        | ~ l1_pre_topc(X50)
        | ~ l1_pre_topc(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).

cnf(c_0_45,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( r1_tarski(k6_partfun1(X1),k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_38])).

fof(c_0_51,plain,(
    ! [X17] : r1_tarski(k1_xboole_0,X17) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_54,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_xboole_0(X29)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X30,X29)))
      | v1_xboole_0(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_55,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_57,plain,(
    ! [X45] :
      ( ~ l1_struct_0(X45)
      | k2_struct_0(X45) = u1_struct_0(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_58,plain,(
    ! [X46] :
      ( ~ l1_pre_topc(X46)
      | l1_struct_0(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_59,plain,
    ( v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( l1_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_63,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_64,negated_conjecture,
    ( ~ v5_pre_topc(esk9_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_65,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,X1),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_67,negated_conjecture,
    ( v1_tdlat_3(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_68,plain,(
    ! [X54,X55,X56,X57] :
      ( ( ~ v5_pre_topc(X56,X54,X55)
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X55)))
        | r1_tarski(k2_pre_topc(X54,k8_relset_1(u1_struct_0(X54),u1_struct_0(X55),X56,X57)),k8_relset_1(u1_struct_0(X54),u1_struct_0(X55),X56,k2_pre_topc(X55,X57)))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,u1_struct_0(X54),u1_struct_0(X55))
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(X55))))
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55)
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54) )
      & ( m1_subset_1(esk4_3(X54,X55,X56),k1_zfmisc_1(u1_struct_0(X55)))
        | v5_pre_topc(X56,X54,X55)
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,u1_struct_0(X54),u1_struct_0(X55))
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(X55))))
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55)
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54) )
      & ( ~ r1_tarski(k2_pre_topc(X54,k8_relset_1(u1_struct_0(X54),u1_struct_0(X55),X56,esk4_3(X54,X55,X56))),k8_relset_1(u1_struct_0(X54),u1_struct_0(X55),X56,k2_pre_topc(X55,esk4_3(X54,X55,X56))))
        | v5_pre_topc(X56,X54,X55)
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,u1_struct_0(X54),u1_struct_0(X55))
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(X55))))
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55)
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_2])])])])])).

cnf(c_0_69,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_70,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_71,plain,(
    ! [X26,X27,X28] :
      ( ( v4_relat_1(X28,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v5_relat_1(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_73,plain,(
    ! [X24,X25] : v1_relat_1(k2_zfmisc_1(X24,X25)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_74,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk9_0,k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_48])).

cnf(c_0_76,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_78,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_79,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_80,negated_conjecture,
    ( k2_struct_0(esk8_0) = k1_xboole_0
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk3_3(esk7_0,esk8_0,esk9_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62]),c_0_63]),c_0_48])]),c_0_64])).

cnf(c_0_81,negated_conjecture,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,X1),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_63])])).

cnf(c_0_82,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_83,negated_conjecture,
    ( v2_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_84,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_85,plain,(
    ! [X42,X43] :
      ( ( ~ v1_partfun1(X43,X42)
        | k1_relat_1(X43) = X42
        | ~ v1_relat_1(X43)
        | ~ v4_relat_1(X43,X42) )
      & ( k1_relat_1(X43) != X42
        | v1_partfun1(X43,X42)
        | ~ v1_relat_1(X43)
        | ~ v4_relat_1(X43,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_86,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_87,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_69]),c_0_70])])).

cnf(c_0_88,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_89,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_70])).

cnf(c_0_90,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_91,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk4_3(X1,X2,X3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk4_3(X1,X2,X3))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_92,negated_conjecture,
    ( k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)) = esk9_0
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_93,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_94,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_95,negated_conjecture,
    ( k2_struct_0(esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])])).

cnf(c_0_96,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk4_3(esk7_0,esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_60]),c_0_61]),c_0_83]),c_0_84]),c_0_62]),c_0_63]),c_0_48])]),c_0_64])).

fof(c_0_98,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k1_relset_1(X36,X37,X38) = k1_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_99,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_100,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_101,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_102,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_50])).

fof(c_0_103,plain,(
    ! [X63,X64] :
      ( ( ~ v1_tdlat_3(X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))
        | v4_pre_topc(X64,X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63) )
      & ( m1_subset_1(esk6_1(X63),k1_zfmisc_1(u1_struct_0(X63)))
        | v1_tdlat_3(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63) )
      & ( ~ v4_pre_topc(esk6_1(X63),X63)
        | v1_tdlat_3(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tdlat_3])])])])])).

cnf(c_0_104,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(esk7_0,k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk4_3(esk7_0,esk8_0,esk9_0))),k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,k2_pre_topc(esk8_0,esk4_3(esk7_0,esk8_0,esk9_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_60]),c_0_61]),c_0_83]),c_0_84]),c_0_62]),c_0_63]),c_0_48])]),c_0_64])).

cnf(c_0_105,negated_conjecture,
    ( k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)) = esk9_0
    | ~ v1_xboole_0(u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_106,negated_conjecture,
    ( u1_struct_0(esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_62])])).

cnf(c_0_107,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_96])).

cnf(c_0_108,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(esk4_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_97])).

fof(c_0_110,plain,(
    ! [X39,X40,X41] :
      ( ( k7_relset_1(X39,X40,X41,X39) = k2_relset_1(X39,X40,X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( k8_relset_1(X39,X40,X41,X40) = k1_relset_1(X39,X40,X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

cnf(c_0_111,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_112,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101]),c_0_102])])).

fof(c_0_113,plain,(
    ! [X47,X48] :
      ( ( ~ v4_pre_topc(X48,X47)
        | k2_pre_topc(X47,X48) = X48
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ l1_pre_topc(X47) )
      & ( ~ v2_pre_topc(X47)
        | k2_pre_topc(X47,X48) != X48
        | v4_pre_topc(X48,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ l1_pre_topc(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_114,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_115,negated_conjecture,
    ( ~ v1_xboole_0(k2_pre_topc(esk7_0,k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk4_3(esk7_0,esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_53])).

cnf(c_0_116,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106]),c_0_107]),c_0_106]),c_0_108])])).

cnf(c_0_117,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,esk9_0) = u1_struct_0(esk8_0)
    | ~ v1_xboole_0(u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_109])).

cnf(c_0_118,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_119,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_89]),c_0_112])).

cnf(c_0_120,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_113])).

cnf(c_0_121,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_114,c_0_46])).

cnf(c_0_122,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_53])).

cnf(c_0_123,negated_conjecture,
    ( ~ v1_xboole_0(k2_pre_topc(esk7_0,k8_relset_1(u1_struct_0(esk7_0),k1_xboole_0,k1_xboole_0,esk4_3(esk7_0,esk8_0,k1_xboole_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_106]),c_0_116]),c_0_116])).

cnf(c_0_124,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_106]),c_0_106]),c_0_108])]),c_0_116])).

cnf(c_0_125,plain,
    ( k8_relset_1(X1,X2,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_89]),c_0_119])).

cnf(c_0_126,plain,
    ( k2_pre_topc(X1,k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_120,c_0_89])).

cnf(c_0_127,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_128,negated_conjecture,
    ( ~ v1_xboole_0(k2_pre_topc(esk7_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_124]),c_0_125])).

cnf(c_0_129,plain,
    ( k2_pre_topc(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_108])])).

cnf(c_0_130,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_108]),c_0_67]),c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n020.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 11:04:37 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  # Version: 2.5pre002
% 0.13/0.32  # No SInE strategy applied
% 0.13/0.32  # Trying AutoSched0 for 299 seconds
% 0.18/0.41  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.18/0.41  # and selection function SelectNewComplexAHPNS.
% 0.18/0.41  #
% 0.18/0.41  # Preprocessing time       : 0.031 s
% 0.18/0.41  # Presaturation interreduction done
% 0.18/0.41  
% 0.18/0.41  # Proof found!
% 0.18/0.41  # SZS status Theorem
% 0.18/0.41  # SZS output start CNFRefutation
% 0.18/0.41  fof(t68_tex_2, conjecture, ![X1]:(((v2_pre_topc(X1)&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>v5_pre_topc(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_tex_2)).
% 0.18/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.41  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.18/0.41  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.18/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.41  fof(t17_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 0.18/0.41  fof(cc1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 0.18/0.41  fof(dt_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 0.18/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.41  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.18/0.41  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.18/0.41  fof(t55_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v3_pre_topc(X4,X2)=>v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_2)).
% 0.18/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.42  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.18/0.42  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.18/0.42  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.18/0.42  fof(t56_tops_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_2)).
% 0.18/0.42  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.18/0.42  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.18/0.42  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.18/0.42  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.18/0.42  fof(t18_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tdlat_3)).
% 0.18/0.42  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.42  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 0.18/0.42  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.18/0.42  fof(c_0_26, negated_conjecture, ~(![X1]:(((v2_pre_topc(X1)&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>v5_pre_topc(X3,X1,X2))))), inference(assume_negation,[status(cth)],[t68_tex_2])).
% 0.18/0.42  fof(c_0_27, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.42  fof(c_0_28, plain, ![X44]:(v1_partfun1(k6_partfun1(X44),X44)&m1_subset_1(k6_partfun1(X44),k1_zfmisc_1(k2_zfmisc_1(X44,X44)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.18/0.42  fof(c_0_29, plain, ![X18, X19]:((k2_zfmisc_1(X18,X19)!=k1_xboole_0|(X18=k1_xboole_0|X19=k1_xboole_0))&((X18!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0)&(X19!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.42  fof(c_0_30, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.18/0.42  fof(c_0_31, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.42  fof(c_0_32, plain, ![X60, X61]:((~v1_tdlat_3(X60)|(~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))|v3_pre_topc(X61,X60))|(~v2_pre_topc(X60)|~l1_pre_topc(X60)))&((m1_subset_1(esk5_1(X60),k1_zfmisc_1(u1_struct_0(X60)))|v1_tdlat_3(X60)|(~v2_pre_topc(X60)|~l1_pre_topc(X60)))&(~v3_pre_topc(esk5_1(X60),X60)|v1_tdlat_3(X60)|(~v2_pre_topc(X60)|~l1_pre_topc(X60))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).
% 0.18/0.42  fof(c_0_33, plain, ![X59]:(~l1_pre_topc(X59)|(~v1_tdlat_3(X59)|v2_pre_topc(X59))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).
% 0.18/0.42  fof(c_0_34, plain, ![X32, X33, X34, X35]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|m1_subset_1(k8_relset_1(X32,X33,X34,X35),k1_zfmisc_1(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).
% 0.18/0.42  fof(c_0_35, negated_conjecture, (((v2_pre_topc(esk7_0)&v1_tdlat_3(esk7_0))&l1_pre_topc(esk7_0))&((v2_pre_topc(esk8_0)&l1_pre_topc(esk8_0))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0)))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)))))&~v5_pre_topc(esk9_0,esk7_0,esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.18/0.42  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.42  cnf(c_0_37, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.42  cnf(c_0_38, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.42  fof(c_0_39, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.42  cnf(c_0_40, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.42  cnf(c_0_41, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.42  fof(c_0_42, plain, ![X21]:m1_subset_1(k2_subset_1(X21),k1_zfmisc_1(X21)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.18/0.42  fof(c_0_43, plain, ![X20]:k2_subset_1(X20)=X20, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.18/0.42  fof(c_0_44, plain, ![X49, X50, X51, X52]:(((~v5_pre_topc(X51,X49,X50)|(~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X50)))|(~v3_pre_topc(X52,X50)|v3_pre_topc(k8_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51,X52),X49)))|k2_struct_0(X50)=k1_xboole_0|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50)))))|~l1_pre_topc(X50)|~l1_pre_topc(X49))&((m1_subset_1(esk3_3(X49,X50,X51),k1_zfmisc_1(u1_struct_0(X50)))|v5_pre_topc(X51,X49,X50)|k2_struct_0(X50)=k1_xboole_0|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50)))))|~l1_pre_topc(X50)|~l1_pre_topc(X49))&((v3_pre_topc(esk3_3(X49,X50,X51),X50)|v5_pre_topc(X51,X49,X50)|k2_struct_0(X50)=k1_xboole_0|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50)))))|~l1_pre_topc(X50)|~l1_pre_topc(X49))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51,esk3_3(X49,X50,X51)),X49)|v5_pre_topc(X51,X49,X50)|k2_struct_0(X50)=k1_xboole_0|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50)))))|~l1_pre_topc(X50)|~l1_pre_topc(X49)))))&((~v5_pre_topc(X51,X49,X50)|(~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X50)))|(~v3_pre_topc(X52,X50)|v3_pre_topc(k8_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51,X52),X49)))|k2_struct_0(X49)!=k1_xboole_0|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50)))))|~l1_pre_topc(X50)|~l1_pre_topc(X49))&((m1_subset_1(esk3_3(X49,X50,X51),k1_zfmisc_1(u1_struct_0(X50)))|v5_pre_topc(X51,X49,X50)|k2_struct_0(X49)!=k1_xboole_0|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50)))))|~l1_pre_topc(X50)|~l1_pre_topc(X49))&((v3_pre_topc(esk3_3(X49,X50,X51),X50)|v5_pre_topc(X51,X49,X50)|k2_struct_0(X49)!=k1_xboole_0|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50)))))|~l1_pre_topc(X50)|~l1_pre_topc(X49))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51,esk3_3(X49,X50,X51)),X49)|v5_pre_topc(X51,X49,X50)|k2_struct_0(X49)!=k1_xboole_0|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50)))))|~l1_pre_topc(X50)|~l1_pre_topc(X49)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).
% 0.18/0.42  cnf(c_0_45, plain, (v3_pre_topc(X2,X1)|~v1_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.42  cnf(c_0_46, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.42  cnf(c_0_47, plain, (m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.42  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.42  cnf(c_0_49, plain, (r1_tarski(k6_partfun1(X1),k2_zfmisc_1(X1,X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.42  cnf(c_0_50, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_38])).
% 0.18/0.42  fof(c_0_51, plain, ![X17]:r1_tarski(k1_xboole_0,X17), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.42  cnf(c_0_52, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.42  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.42  fof(c_0_54, plain, ![X29, X30, X31]:(~v1_xboole_0(X29)|(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X30,X29)))|v1_xboole_0(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.18/0.42  cnf(c_0_55, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.42  cnf(c_0_56, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.42  fof(c_0_57, plain, ![X45]:(~l1_struct_0(X45)|k2_struct_0(X45)=u1_struct_0(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.18/0.42  fof(c_0_58, plain, ![X46]:(~l1_pre_topc(X46)|l1_struct_0(X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.18/0.42  cnf(c_0_59, plain, (v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_3(X1,X2,X3)),X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.42  cnf(c_0_60, negated_conjecture, (v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.42  cnf(c_0_61, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.42  cnf(c_0_62, negated_conjecture, (l1_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.42  cnf(c_0_63, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.42  cnf(c_0_64, negated_conjecture, (~v5_pre_topc(esk9_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.42  cnf(c_0_65, plain, (v3_pre_topc(X1,X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_45, c_0_46])).
% 0.18/0.42  cnf(c_0_66, negated_conjecture, (m1_subset_1(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,X1),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.18/0.42  cnf(c_0_67, negated_conjecture, (v1_tdlat_3(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.42  fof(c_0_68, plain, ![X54, X55, X56, X57]:((~v5_pre_topc(X56,X54,X55)|(~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X55)))|r1_tarski(k2_pre_topc(X54,k8_relset_1(u1_struct_0(X54),u1_struct_0(X55),X56,X57)),k8_relset_1(u1_struct_0(X54),u1_struct_0(X55),X56,k2_pre_topc(X55,X57))))|(~v1_funct_1(X56)|~v1_funct_2(X56,u1_struct_0(X54),u1_struct_0(X55))|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(X55)))))|(~v2_pre_topc(X55)|~l1_pre_topc(X55))|(~v2_pre_topc(X54)|~l1_pre_topc(X54)))&((m1_subset_1(esk4_3(X54,X55,X56),k1_zfmisc_1(u1_struct_0(X55)))|v5_pre_topc(X56,X54,X55)|(~v1_funct_1(X56)|~v1_funct_2(X56,u1_struct_0(X54),u1_struct_0(X55))|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(X55)))))|(~v2_pre_topc(X55)|~l1_pre_topc(X55))|(~v2_pre_topc(X54)|~l1_pre_topc(X54)))&(~r1_tarski(k2_pre_topc(X54,k8_relset_1(u1_struct_0(X54),u1_struct_0(X55),X56,esk4_3(X54,X55,X56))),k8_relset_1(u1_struct_0(X54),u1_struct_0(X55),X56,k2_pre_topc(X55,esk4_3(X54,X55,X56))))|v5_pre_topc(X56,X54,X55)|(~v1_funct_1(X56)|~v1_funct_2(X56,u1_struct_0(X54),u1_struct_0(X55))|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(X55)))))|(~v2_pre_topc(X55)|~l1_pre_topc(X55))|(~v2_pre_topc(X54)|~l1_pre_topc(X54))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_2])])])])])).
% 0.18/0.42  cnf(c_0_69, plain, (r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.18/0.42  cnf(c_0_70, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.18/0.42  fof(c_0_71, plain, ![X26, X27, X28]:((v4_relat_1(X28,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(v5_relat_1(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.18/0.42  cnf(c_0_72, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.42  fof(c_0_73, plain, ![X24, X25]:v1_relat_1(k2_zfmisc_1(X24,X25)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.18/0.42  cnf(c_0_74, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.18/0.42  cnf(c_0_75, negated_conjecture, (r1_tarski(esk9_0,k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)))), inference(spm,[status(thm)],[c_0_36, c_0_48])).
% 0.18/0.42  cnf(c_0_76, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.18/0.42  cnf(c_0_77, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.18/0.42  cnf(c_0_78, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.18/0.42  cnf(c_0_79, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.42  cnf(c_0_80, negated_conjecture, (k2_struct_0(esk8_0)=k1_xboole_0|~v3_pre_topc(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk3_3(esk7_0,esk8_0,esk9_0)),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62]), c_0_63]), c_0_48])]), c_0_64])).
% 0.18/0.42  cnf(c_0_81, negated_conjecture, (v3_pre_topc(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,X1),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_63])])).
% 0.18/0.42  cnf(c_0_82, plain, (m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.18/0.42  cnf(c_0_83, negated_conjecture, (v2_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.42  cnf(c_0_84, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.42  fof(c_0_85, plain, ![X42, X43]:((~v1_partfun1(X43,X42)|k1_relat_1(X43)=X42|(~v1_relat_1(X43)|~v4_relat_1(X43,X42)))&(k1_relat_1(X43)!=X42|v1_partfun1(X43,X42)|(~v1_relat_1(X43)|~v4_relat_1(X43,X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.18/0.42  cnf(c_0_86, plain, (v1_partfun1(k6_partfun1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.42  cnf(c_0_87, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_69]), c_0_70])])).
% 0.18/0.42  cnf(c_0_88, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.18/0.42  cnf(c_0_89, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_72, c_0_70])).
% 0.18/0.42  cnf(c_0_90, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.18/0.42  cnf(c_0_91, plain, (v5_pre_topc(X3,X1,X2)|~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk4_3(X1,X2,X3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk4_3(X1,X2,X3))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.18/0.42  cnf(c_0_92, negated_conjecture, (k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))=esk9_0|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.18/0.42  cnf(c_0_93, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.18/0.42  cnf(c_0_94, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.18/0.42  cnf(c_0_95, negated_conjecture, (k2_struct_0(esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])])).
% 0.18/0.42  cnf(c_0_96, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.42  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk4_3(esk7_0,esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_60]), c_0_61]), c_0_83]), c_0_84]), c_0_62]), c_0_63]), c_0_48])]), c_0_64])).
% 0.18/0.42  fof(c_0_98, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k1_relset_1(X36,X37,X38)=k1_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.18/0.42  cnf(c_0_99, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.18/0.42  cnf(c_0_100, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.18/0.42  cnf(c_0_101, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.18/0.42  cnf(c_0_102, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_90, c_0_50])).
% 0.18/0.42  fof(c_0_103, plain, ![X63, X64]:((~v1_tdlat_3(X63)|(~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))|v4_pre_topc(X64,X63))|(~v2_pre_topc(X63)|~l1_pre_topc(X63)))&((m1_subset_1(esk6_1(X63),k1_zfmisc_1(u1_struct_0(X63)))|v1_tdlat_3(X63)|(~v2_pre_topc(X63)|~l1_pre_topc(X63)))&(~v4_pre_topc(esk6_1(X63),X63)|v1_tdlat_3(X63)|(~v2_pre_topc(X63)|~l1_pre_topc(X63))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tdlat_3])])])])])).
% 0.18/0.42  cnf(c_0_104, negated_conjecture, (~r1_tarski(k2_pre_topc(esk7_0,k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk4_3(esk7_0,esk8_0,esk9_0))),k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,k2_pre_topc(esk8_0,esk4_3(esk7_0,esk8_0,esk9_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_60]), c_0_61]), c_0_83]), c_0_84]), c_0_62]), c_0_63]), c_0_48])]), c_0_64])).
% 0.18/0.42  cnf(c_0_105, negated_conjecture, (k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))=esk9_0|~v1_xboole_0(u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.18/0.42  cnf(c_0_106, negated_conjecture, (u1_struct_0(esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_62])])).
% 0.18/0.42  cnf(c_0_107, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_96])).
% 0.18/0.42  cnf(c_0_108, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.42  cnf(c_0_109, negated_conjecture, (r1_tarski(esk4_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_36, c_0_97])).
% 0.18/0.42  fof(c_0_110, plain, ![X39, X40, X41]:((k7_relset_1(X39,X40,X41,X39)=k2_relset_1(X39,X40,X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(k8_relset_1(X39,X40,X41,X40)=k1_relset_1(X39,X40,X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.18/0.42  cnf(c_0_111, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.18/0.42  cnf(c_0_112, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_101]), c_0_102])])).
% 0.18/0.42  fof(c_0_113, plain, ![X47, X48]:((~v4_pre_topc(X48,X47)|k2_pre_topc(X47,X48)=X48|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|~l1_pre_topc(X47))&(~v2_pre_topc(X47)|k2_pre_topc(X47,X48)!=X48|v4_pre_topc(X48,X47)|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|~l1_pre_topc(X47))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.18/0.42  cnf(c_0_114, plain, (v4_pre_topc(X2,X1)|~v1_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.18/0.42  cnf(c_0_115, negated_conjecture, (~v1_xboole_0(k2_pre_topc(esk7_0,k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk4_3(esk7_0,esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_104, c_0_53])).
% 0.18/0.42  cnf(c_0_116, negated_conjecture, (esk9_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_106]), c_0_107]), c_0_106]), c_0_108])])).
% 0.18/0.42  cnf(c_0_117, negated_conjecture, (esk4_3(esk7_0,esk8_0,esk9_0)=u1_struct_0(esk8_0)|~v1_xboole_0(u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_74, c_0_109])).
% 0.18/0.42  cnf(c_0_118, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_110])).
% 0.18/0.42  cnf(c_0_119, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_89]), c_0_112])).
% 0.18/0.42  cnf(c_0_120, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_113])).
% 0.18/0.42  cnf(c_0_121, plain, (v4_pre_topc(X1,X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_114, c_0_46])).
% 0.18/0.42  cnf(c_0_122, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_72, c_0_53])).
% 0.18/0.42  cnf(c_0_123, negated_conjecture, (~v1_xboole_0(k2_pre_topc(esk7_0,k8_relset_1(u1_struct_0(esk7_0),k1_xboole_0,k1_xboole_0,esk4_3(esk7_0,esk8_0,k1_xboole_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_106]), c_0_116]), c_0_116])).
% 0.18/0.42  cnf(c_0_124, negated_conjecture, (esk4_3(esk7_0,esk8_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_106]), c_0_106]), c_0_108])]), c_0_116])).
% 0.18/0.42  cnf(c_0_125, plain, (k8_relset_1(X1,X2,k1_xboole_0,X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_89]), c_0_119])).
% 0.18/0.42  cnf(c_0_126, plain, (k2_pre_topc(X1,k1_xboole_0)=k1_xboole_0|~v4_pre_topc(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_120, c_0_89])).
% 0.18/0.42  cnf(c_0_127, plain, (v4_pre_topc(X1,X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 0.18/0.42  cnf(c_0_128, negated_conjecture, (~v1_xboole_0(k2_pre_topc(esk7_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_124]), c_0_125])).
% 0.18/0.42  cnf(c_0_129, plain, (k2_pre_topc(X1,k1_xboole_0)=k1_xboole_0|~v1_tdlat_3(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_108])])).
% 0.18/0.42  cnf(c_0_130, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_108]), c_0_67]), c_0_63])]), ['proof']).
% 0.18/0.42  # SZS output end CNFRefutation
% 0.18/0.42  # Proof object total steps             : 131
% 0.18/0.42  # Proof object clause steps            : 79
% 0.18/0.42  # Proof object formula steps           : 52
% 0.18/0.42  # Proof object conjectures             : 30
% 0.18/0.42  # Proof object clause conjectures      : 27
% 0.18/0.42  # Proof object formula conjectures     : 3
% 0.18/0.42  # Proof object initial clauses used    : 38
% 0.18/0.42  # Proof object initial formulas used   : 26
% 0.18/0.42  # Proof object generating inferences   : 31
% 0.18/0.42  # Proof object simplifying inferences  : 62
% 0.18/0.42  # Training examples: 0 positive, 0 negative
% 0.18/0.42  # Parsed axioms                        : 26
% 0.18/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.42  # Initial clauses                      : 60
% 0.18/0.42  # Removed in clause preprocessing      : 1
% 0.18/0.42  # Initial clauses in saturation        : 59
% 0.18/0.42  # Processed clauses                    : 586
% 0.18/0.42  # ...of these trivial                  : 16
% 0.18/0.42  # ...subsumed                          : 239
% 0.18/0.42  # ...remaining for further processing  : 331
% 0.18/0.42  # Other redundant clauses eliminated   : 21
% 0.18/0.42  # Clauses deleted for lack of memory   : 0
% 0.18/0.42  # Backward-subsumed                    : 6
% 0.18/0.42  # Backward-rewritten                   : 84
% 0.18/0.42  # Generated clauses                    : 2127
% 0.18/0.42  # ...of the previous two non-trivial   : 1818
% 0.18/0.42  # Contextual simplify-reflections      : 2
% 0.18/0.42  # Paramodulations                      : 2106
% 0.18/0.42  # Factorizations                       : 0
% 0.18/0.42  # Equation resolutions                 : 21
% 0.18/0.42  # Propositional unsat checks           : 0
% 0.18/0.42  #    Propositional check models        : 0
% 0.18/0.42  #    Propositional check unsatisfiable : 0
% 0.18/0.42  #    Propositional clauses             : 0
% 0.18/0.42  #    Propositional clauses after purity: 0
% 0.18/0.42  #    Propositional unsat core size     : 0
% 0.18/0.42  #    Propositional preprocessing time  : 0.000
% 0.18/0.42  #    Propositional encoding time       : 0.000
% 0.18/0.42  #    Propositional solver time         : 0.000
% 0.18/0.42  #    Success case prop preproc time    : 0.000
% 0.18/0.42  #    Success case prop encoding time   : 0.000
% 0.18/0.42  #    Success case prop solver time     : 0.000
% 0.18/0.42  # Current number of processed clauses  : 178
% 0.18/0.42  #    Positive orientable unit clauses  : 50
% 0.18/0.42  #    Positive unorientable unit clauses: 2
% 0.18/0.42  #    Negative unit clauses             : 2
% 0.18/0.42  #    Non-unit-clauses                  : 124
% 0.18/0.42  # Current number of unprocessed clauses: 1339
% 0.18/0.42  # ...number of literals in the above   : 5943
% 0.18/0.42  # Current number of archived formulas  : 0
% 0.18/0.42  # Current number of archived clauses   : 149
% 0.18/0.42  # Clause-clause subsumption calls (NU) : 19953
% 0.18/0.42  # Rec. Clause-clause subsumption calls : 4542
% 0.18/0.42  # Non-unit clause-clause subsumptions  : 240
% 0.18/0.42  # Unit Clause-clause subsumption calls : 565
% 0.18/0.42  # Rewrite failures with RHS unbound    : 0
% 0.18/0.42  # BW rewrite match attempts            : 169
% 0.18/0.42  # BW rewrite match successes           : 15
% 0.18/0.42  # Condensation attempts                : 0
% 0.18/0.42  # Condensation successes               : 0
% 0.18/0.42  # Termbank termtop insertions          : 35319
% 0.18/0.42  
% 0.18/0.42  # -------------------------------------------------
% 0.18/0.42  # User time                : 0.089 s
% 0.18/0.42  # System time              : 0.007 s
% 0.18/0.42  # Total time               : 0.096 s
% 0.18/0.42  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
