%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : compts_1__t26_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:50 EDT 2019

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 586 expanded)
%              Number of clauses        :   51 ( 188 expanded)
%              Number of leaves         :   15 ( 145 expanded)
%              Depth                    :   11
%              Number of atoms          :  393 (5992 expanded)
%              Number of equality atoms :   49 ( 798 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   79 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_compts_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( v1_compts_1(X1)
                  & v8_pre_topc(X2)
                  & k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3)
                  & v5_pre_topc(X3,X1,X2) )
               => v3_tops_2(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t26_compts_1.p',t26_compts_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t26_compts_1.p',redefinition_k1_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t26_compts_1.p',cc1_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t26_compts_1.p',redefinition_k7_relset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t26_compts_1.p',redefinition_k8_relset_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t26_compts_1.p',t146_funct_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t26_compts_1.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t26_compts_1.p',dt_l1_pre_topc)).

fof(t72_tops_2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/compts_1__t26_compts_1.p',t72_tops_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t26_compts_1.p',t3_subset)).

fof(t152_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t26_compts_1.p',t152_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/compts_1__t26_compts_1.p',d12_pre_topc)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t26_compts_1.p',dt_k7_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t26_compts_1.p',d10_xboole_0)).

fof(t25_compts_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( v1_compts_1(X1)
                  & v8_pre_topc(X2)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v5_pre_topc(X3,X1,X2) )
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X4,X1)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t26_compts_1.p',t25_compts_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( ( v1_compts_1(X1)
                    & v8_pre_topc(X2)
                    & k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                    & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                    & v2_funct_1(X3)
                    & v5_pre_topc(X3,X1,X2) )
                 => v3_tops_2(X3,X1,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_compts_1])).

fof(c_0_16,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k1_relset_1(X41,X42,X43) = k1_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v1_compts_1(esk1_0)
    & v8_pre_topc(esk2_0)
    & k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk1_0)
    & k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0)
    & v2_funct_1(esk3_0)
    & v5_pre_topc(esk3_0,esk1_0,esk2_0)
    & ~ v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X85,X86,X87] :
      ( ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86)))
      | v1_relat_1(X87) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_19,plain,(
    ! [X47,X48,X49,X50] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k7_relset_1(X47,X48,X49,X50) = k9_relat_1(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_20,plain,(
    ! [X51,X52,X53,X54] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | k8_relset_1(X51,X52,X53,X54) = k10_relat_1(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_21,plain,(
    ! [X55,X56] :
      ( ~ v1_relat_1(X56)
      | ~ r1_tarski(X55,k1_relat_1(X56))
      | r1_tarski(X55,k10_relat_1(X56,k9_relat_1(X56,X55))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_22,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X20] :
      ( ~ l1_struct_0(X20)
      | k2_struct_0(X20) = u1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_29,plain,(
    ! [X36] :
      ( ~ l1_pre_topc(X36)
      | l1_struct_0(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_30,plain,(
    ! [X76,X77,X78,X79] :
      ( ( k1_relset_1(u1_struct_0(X76),u1_struct_0(X77),X78) = k2_struct_0(X76)
        | ~ v3_tops_2(X78,X76,X77)
        | ~ v1_funct_1(X78)
        | ~ v1_funct_2(X78,u1_struct_0(X76),u1_struct_0(X77))
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X76),u1_struct_0(X77))))
        | v2_struct_0(X77)
        | ~ l1_pre_topc(X77)
        | ~ l1_pre_topc(X76) )
      & ( k2_relset_1(u1_struct_0(X76),u1_struct_0(X77),X78) = k2_struct_0(X77)
        | ~ v3_tops_2(X78,X76,X77)
        | ~ v1_funct_1(X78)
        | ~ v1_funct_2(X78,u1_struct_0(X76),u1_struct_0(X77))
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X76),u1_struct_0(X77))))
        | v2_struct_0(X77)
        | ~ l1_pre_topc(X77)
        | ~ l1_pre_topc(X76) )
      & ( v2_funct_1(X78)
        | ~ v3_tops_2(X78,X76,X77)
        | ~ v1_funct_1(X78)
        | ~ v1_funct_2(X78,u1_struct_0(X76),u1_struct_0(X77))
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X76),u1_struct_0(X77))))
        | v2_struct_0(X77)
        | ~ l1_pre_topc(X77)
        | ~ l1_pre_topc(X76) )
      & ( ~ v4_pre_topc(X79,X76)
        | v4_pre_topc(k7_relset_1(u1_struct_0(X76),u1_struct_0(X77),X78,X79),X77)
        | ~ m1_subset_1(X79,k1_zfmisc_1(u1_struct_0(X76)))
        | ~ v3_tops_2(X78,X76,X77)
        | ~ v1_funct_1(X78)
        | ~ v1_funct_2(X78,u1_struct_0(X76),u1_struct_0(X77))
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X76),u1_struct_0(X77))))
        | v2_struct_0(X77)
        | ~ l1_pre_topc(X77)
        | ~ l1_pre_topc(X76) )
      & ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X76),u1_struct_0(X77),X78,X79),X77)
        | v4_pre_topc(X79,X76)
        | ~ m1_subset_1(X79,k1_zfmisc_1(u1_struct_0(X76)))
        | ~ v3_tops_2(X78,X76,X77)
        | ~ v1_funct_1(X78)
        | ~ v1_funct_2(X78,u1_struct_0(X76),u1_struct_0(X77))
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X76),u1_struct_0(X77))))
        | v2_struct_0(X77)
        | ~ l1_pre_topc(X77)
        | ~ l1_pre_topc(X76) )
      & ( m1_subset_1(esk8_3(X76,X77,X78),k1_zfmisc_1(u1_struct_0(X76)))
        | k1_relset_1(u1_struct_0(X76),u1_struct_0(X77),X78) != k2_struct_0(X76)
        | k2_relset_1(u1_struct_0(X76),u1_struct_0(X77),X78) != k2_struct_0(X77)
        | ~ v2_funct_1(X78)
        | v3_tops_2(X78,X76,X77)
        | ~ v1_funct_1(X78)
        | ~ v1_funct_2(X78,u1_struct_0(X76),u1_struct_0(X77))
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X76),u1_struct_0(X77))))
        | v2_struct_0(X77)
        | ~ l1_pre_topc(X77)
        | ~ l1_pre_topc(X76) )
      & ( ~ v4_pre_topc(esk8_3(X76,X77,X78),X76)
        | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X76),u1_struct_0(X77),X78,esk8_3(X76,X77,X78)),X77)
        | k1_relset_1(u1_struct_0(X76),u1_struct_0(X77),X78) != k2_struct_0(X76)
        | k2_relset_1(u1_struct_0(X76),u1_struct_0(X77),X78) != k2_struct_0(X77)
        | ~ v2_funct_1(X78)
        | v3_tops_2(X78,X76,X77)
        | ~ v1_funct_1(X78)
        | ~ v1_funct_2(X78,u1_struct_0(X76),u1_struct_0(X77))
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X76),u1_struct_0(X77))))
        | v2_struct_0(X77)
        | ~ l1_pre_topc(X77)
        | ~ l1_pre_topc(X76) )
      & ( v4_pre_topc(esk8_3(X76,X77,X78),X76)
        | v4_pre_topc(k7_relset_1(u1_struct_0(X76),u1_struct_0(X77),X78,esk8_3(X76,X77,X78)),X77)
        | k1_relset_1(u1_struct_0(X76),u1_struct_0(X77),X78) != k2_struct_0(X76)
        | k2_relset_1(u1_struct_0(X76),u1_struct_0(X77),X78) != k2_struct_0(X77)
        | ~ v2_funct_1(X78)
        | v3_tops_2(X78,X76,X77)
        | ~ v1_funct_1(X78)
        | ~ v1_funct_2(X78,u1_struct_0(X76),u1_struct_0(X77))
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X76),u1_struct_0(X77))))
        | v2_struct_0(X77)
        | ~ l1_pre_topc(X77)
        | ~ l1_pre_topc(X76) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_tops_2])])])])])])).

cnf(c_0_31,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(esk3_0) = k2_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( k9_relat_1(esk3_0,X1) = k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( k10_relat_1(esk3_0,X1) = k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_36,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X67,X68] :
      ( ( ~ m1_subset_1(X67,k1_zfmisc_1(X68))
        | r1_tarski(X67,X68) )
      & ( ~ r1_tarski(X67,X68)
        | m1_subset_1(X67,k1_zfmisc_1(X68)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tops_2(X3,X1,X2)
    | v2_struct_0(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( ~ v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(X1,k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1)))
    | ~ r1_tarski(X1,k2_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_34]),c_0_35])).

cnf(c_0_49,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_24]),c_0_41]),c_0_23]),c_0_42]),c_0_43]),c_0_44]),c_0_45])]),c_0_46]),c_0_47])).

fof(c_0_52,plain,(
    ! [X57,X58] :
      ( ~ v1_relat_1(X58)
      | ~ v1_funct_1(X58)
      | ~ v2_funct_1(X58)
      | r1_tarski(k10_relat_1(X58,k9_relat_1(X58,X57)),X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_funct_1])])).

fof(c_0_53,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ v5_pre_topc(X14,X12,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ v4_pre_topc(X15,X13)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X12),u1_struct_0(X13),X14,X15),X12)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk4_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X13)))
        | v5_pre_topc(X14,X12,X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) )
      & ( v4_pre_topc(esk4_3(X12,X13,X14),X13)
        | v5_pre_topc(X14,X12,X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X12),u1_struct_0(X13),X14,esk4_3(X12,X13,X14)),X12)
        | v5_pre_topc(X14,X12,X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

fof(c_0_54,plain,(
    ! [X28,X29,X30,X31] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | m1_subset_1(k7_relset_1(X28,X29,X30,X31),k1_zfmisc_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

fof(c_0_55,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(X1,k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1)))
    | ~ r1_tarski(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_45])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk8_3(esk1_0,esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_61,plain,
    ( v4_pre_topc(esk8_3(X1,X2,X3),X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk8_3(X1,X2,X3)),X2)
    | v3_tops_2(X3,X1,X2)
    | v2_struct_0(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_62,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk8_3(esk1_0,esk2_0,esk3_0),k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk8_3(esk1_0,esk2_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1)),X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_35]),c_0_33]),c_0_41]),c_0_43])]),c_0_34])).

fof(c_0_66,plain,(
    ! [X61,X62,X63,X64] :
      ( ~ v2_pre_topc(X61)
      | ~ l1_pre_topc(X61)
      | v2_struct_0(X62)
      | ~ v2_pre_topc(X62)
      | ~ l1_pre_topc(X62)
      | ~ v1_funct_1(X63)
      | ~ v1_funct_2(X63,u1_struct_0(X61),u1_struct_0(X62))
      | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X61),u1_struct_0(X62))))
      | ~ v1_compts_1(X61)
      | ~ v8_pre_topc(X62)
      | k2_relset_1(u1_struct_0(X61),u1_struct_0(X62),X63) != k2_struct_0(X62)
      | ~ v5_pre_topc(X63,X61,X62)
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X61)))
      | ~ v4_pre_topc(X64,X61)
      | v4_pre_topc(k7_relset_1(u1_struct_0(X61),u1_struct_0(X62),X63,X64),X62) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_compts_1])])])])).

cnf(c_0_67,plain,
    ( v3_tops_2(X3,X1,X2)
    | v2_struct_0(X2)
    | ~ v4_pre_topc(esk8_3(X1,X2,X3),X1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk8_3(X1,X2,X3)),X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_68,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1),esk1_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_23]),c_0_42]),c_0_43]),c_0_44]),c_0_45])])).

cnf(c_0_69,negated_conjecture,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk8_3(esk1_0,esk2_0,esk3_0)),esk2_0)
    | v4_pre_topc(esk8_3(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_40]),c_0_24]),c_0_41]),c_0_23]),c_0_42]),c_0_43]),c_0_44]),c_0_45])]),c_0_46]),c_0_47])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_23])).

cnf(c_0_71,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk8_3(esk1_0,esk2_0,esk3_0))) = esk8_3(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

cnf(c_0_72,plain,
    ( v2_struct_0(X2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_compts_1(X1)
    | ~ v8_pre_topc(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( v8_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_74,negated_conjecture,
    ( v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_75,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_76,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_77,negated_conjecture,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk8_3(esk1_0,esk2_0,esk3_0)),esk2_0)
    | ~ v4_pre_topc(esk8_3(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_40]),c_0_24]),c_0_41]),c_0_23]),c_0_42]),c_0_43]),c_0_44]),c_0_45])]),c_0_46]),c_0_47])).

cnf(c_0_78,negated_conjecture,
    ( v4_pre_topc(esk8_3(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])]),c_0_71])])).

cnf(c_0_79,negated_conjecture,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1),esk2_0)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_60]),c_0_40]),c_0_73]),c_0_74]),c_0_23]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_75]),c_0_76])]),c_0_47])).

cnf(c_0_80,negated_conjecture,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk8_3(esk1_0,esk2_0,esk3_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78])])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_78]),c_0_51])]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
