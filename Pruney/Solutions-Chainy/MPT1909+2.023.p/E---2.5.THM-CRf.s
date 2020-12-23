%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:05 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 484 expanded)
%              Number of clauses        :   63 ( 175 expanded)
%              Number of leaves         :   19 ( 126 expanded)
%              Depth                    :   12
%              Number of atoms          :  342 (3604 expanded)
%              Number of equality atoms :   58 ( 480 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v4_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t77_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_tex_2(X2,X1)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & v5_pre_topc(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v3_borsuk_1(X3,X1,X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ( X4 = X5
                         => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k6_domain_1(u1_struct_0(X2),X4)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).

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

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t46_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ v3_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(redefinition_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(t76_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_tex_2(X2,X1)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & v5_pre_topc(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v3_borsuk_1(X3,X1,X2)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( X4 = X5
                         => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k2_pre_topc(X1,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(dt_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(c_0_19,plain,(
    ! [X61,X62,X63] :
      ( ( ~ v4_tex_2(X62,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X61)))
        | X63 != u1_struct_0(X62)
        | v3_tex_2(X63,X61)
        | ~ m1_pre_topc(X62,X61)
        | v2_struct_0(X61)
        | ~ l1_pre_topc(X61) )
      & ( m1_subset_1(esk3_2(X61,X62),k1_zfmisc_1(u1_struct_0(X61)))
        | v4_tex_2(X62,X61)
        | ~ m1_pre_topc(X62,X61)
        | v2_struct_0(X61)
        | ~ l1_pre_topc(X61) )
      & ( esk3_2(X61,X62) = u1_struct_0(X62)
        | v4_tex_2(X62,X61)
        | ~ m1_pre_topc(X62,X61)
        | v2_struct_0(X61)
        | ~ l1_pre_topc(X61) )
      & ( ~ v3_tex_2(esk3_2(X61,X62),X61)
        | v4_tex_2(X62,X61)
        | ~ m1_pre_topc(X62,X61)
        | v2_struct_0(X61)
        | ~ l1_pre_topc(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tex_2])])])])])])).

fof(c_0_20,plain,(
    ! [X59,X60] :
      ( ~ l1_pre_topc(X59)
      | ~ m1_pre_topc(X60,X59)
      | m1_subset_1(u1_struct_0(X60),k1_zfmisc_1(u1_struct_0(X59))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_tex_2(X2,X1)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & v5_pre_topc(X3,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( v3_borsuk_1(X3,X1,X2)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X2))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( X4 = X5
                           => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k6_domain_1(u1_struct_0(X2),X4)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X5)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_tex_2])).

fof(c_0_22,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_23,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_tarski(X15,X16) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_24,plain,(
    ! [X54,X55] :
      ( v1_xboole_0(X54)
      | ~ m1_subset_1(X55,X54)
      | k6_domain_1(X54,X55) = k1_tarski(X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_25,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X24,X25,X26,X27] : k3_enumset1(X24,X24,X25,X26,X27) = k2_enumset1(X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X28,X29,X30,X31,X32] : k4_enumset1(X28,X28,X29,X30,X31,X32) = k3_enumset1(X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_30,plain,(
    ! [X33,X34,X35,X36,X37,X38] : k5_enumset1(X33,X33,X34,X35,X36,X37,X38) = k4_enumset1(X33,X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_31,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45] : k6_enumset1(X39,X39,X40,X41,X42,X43,X44,X45) = k5_enumset1(X39,X40,X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_32,plain,
    ( v3_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ v4_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & v3_tdlat_3(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & v4_tex_2(esk5_0,esk4_0)
    & m1_pre_topc(esk5_0,esk4_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))
    & v5_pre_topc(esk6_0,esk4_0,esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))
    & v3_borsuk_1(esk6_0,esk4_0,esk5_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk4_0))
    & esk7_0 = esk8_0
    & k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0)) != k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_35,plain,(
    ! [X46,X47] :
      ( ( ~ m1_subset_1(X46,k1_zfmisc_1(X47))
        | r1_tarski(X46,X47) )
      & ( ~ r1_tarski(X46,X47)
        | m1_subset_1(X46,k1_zfmisc_1(X47)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_36,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_46,plain,(
    ! [X65,X66] :
      ( v2_struct_0(X65)
      | ~ v2_pre_topc(X65)
      | ~ l1_pre_topc(X65)
      | ~ v1_xboole_0(X66)
      | ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))
      | ~ v3_tex_2(X66,X65) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_tex_2])])])])).

cnf(c_0_47,plain,
    ( v3_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | ~ v4_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( v4_tex_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_54,plain,(
    ! [X56,X57,X58] :
      ( v1_xboole_0(X56)
      | ~ m1_subset_1(X57,X56)
      | ~ m1_subset_1(X58,X56)
      | k7_domain_1(X56,X57,X58) = k2_tarski(X57,X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).

cnf(c_0_55,plain,
    ( k6_domain_1(X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])]),c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) = k6_domain_1(u1_struct_0(esk5_0),esk7_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_50])]),c_0_51]),c_0_60])).

fof(c_0_64,plain,(
    ! [X67,X68,X69,X70,X71] :
      ( v2_struct_0(X67)
      | ~ v2_pre_topc(X67)
      | ~ v3_tdlat_3(X67)
      | ~ l1_pre_topc(X67)
      | v2_struct_0(X68)
      | ~ v4_tex_2(X68,X67)
      | ~ m1_pre_topc(X68,X67)
      | ~ v1_funct_1(X69)
      | ~ v1_funct_2(X69,u1_struct_0(X67),u1_struct_0(X68))
      | ~ v5_pre_topc(X69,X67,X68)
      | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X67),u1_struct_0(X68))))
      | ~ v3_borsuk_1(X69,X67,X68)
      | ~ m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X68)))
      | ~ m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X67)))
      | X70 != X71
      | k8_relset_1(u1_struct_0(X67),u1_struct_0(X68),X69,X70) = k2_pre_topc(X67,X71) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t76_tex_2])])])])).

fof(c_0_65,plain,(
    ! [X48,X49,X50] :
      ( ~ l1_pre_topc(X48)
      | ~ m1_pre_topc(X49,X48)
      | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
      | m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

cnf(c_0_66,plain,
    ( k7_domain_1(X1,X2,X3) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_67,negated_conjecture,
    ( k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) = k6_domain_1(u1_struct_0(esk5_0),esk7_0) ),
    inference(sr,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_69,negated_conjecture,
    ( esk7_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_70,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k2_pre_topc(X1,X5)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v3_borsuk_1(X3,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | X4 != X5 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_74,plain,(
    ! [X51,X52,X53] :
      ( v1_xboole_0(X51)
      | ~ m1_subset_1(X52,X51)
      | ~ m1_subset_1(X53,X51)
      | m1_subset_1(k7_domain_1(X51,X52,X53),k1_zfmisc_1(X51)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_domain_1])])])).

cnf(c_0_75,negated_conjecture,
    ( k7_domain_1(X1,esk7_0,esk7_0) = k6_domain_1(u1_struct_0(esk5_0),esk7_0)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0)) != k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_79,plain,
    ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k2_pre_topc(X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v3_borsuk_1(X3,X1,X2)
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v4_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_72]),c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_81,negated_conjecture,
    ( v3_borsuk_1(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_82,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_83,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_85,negated_conjecture,
    ( v3_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_86,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_87,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_88,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk5_0),esk7_0,esk7_0) = k6_domain_1(u1_struct_0(esk5_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_56]),c_0_63])).

cnf(c_0_89,negated_conjecture,
    ( k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) = k6_domain_1(u1_struct_0(esk4_0),esk7_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_76])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_struct_0(X3)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_33])).

cnf(c_0_91,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_92,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0)) != k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk7_0)) ),
    inference(rw,[status(thm)],[c_0_78,c_0_69])).

cnf(c_0_93,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1) = k2_pre_topc(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_82]),c_0_83]),c_0_84]),c_0_85]),c_0_59]),c_0_48]),c_0_49]),c_0_50])]),c_0_51]),c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_56])]),c_0_63])).

cnf(c_0_95,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk5_0),esk7_0) = k6_domain_1(u1_struct_0(esk4_0),esk7_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_89])).

cnf(c_0_96,plain,
    ( r2_hidden(esk1_1(u1_struct_0(X1)),u1_struct_0(X2))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0)) != k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])])).

cnf(c_0_98,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk5_0),esk7_0) = k6_domain_1(u1_struct_0(esk4_0),esk7_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[c_0_95,c_0_63])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk1_1(u1_struct_0(esk5_0)),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_49]),c_0_50])]),c_0_63])).

cnf(c_0_100,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_99]),c_0_100])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:01:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.18/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.029 s
% 0.18/0.39  # Presaturation interreduction done
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(d8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(v4_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_tex_2(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tex_2)).
% 0.18/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.18/0.39  fof(t77_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_tex_2(X2,X1))&m1_pre_topc(X2,X1))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_borsuk_1(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(X4=X5=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k6_domain_1(u1_struct_0(X2),X4))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X5))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 0.18/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.18/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.39  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.18/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.18/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.18/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.18/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.39  fof(t46_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~(v3_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 0.18/0.39  fof(redefinition_k7_domain_1, axiom, ![X1, X2, X3]:(((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))&m1_subset_1(X3,X1))=>k7_domain_1(X1,X2,X3)=k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_domain_1)).
% 0.18/0.39  fof(t76_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_tex_2(X2,X1))&m1_pre_topc(X2,X1))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_borsuk_1(X3,X1,X2)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=X5=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k2_pre_topc(X1,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 0.18/0.39  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.18/0.39  fof(dt_k7_domain_1, axiom, ![X1, X2, X3]:(((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))&m1_subset_1(X3,X1))=>m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_domain_1)).
% 0.18/0.39  fof(c_0_19, plain, ![X61, X62, X63]:((~v4_tex_2(X62,X61)|(~m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X61)))|(X63!=u1_struct_0(X62)|v3_tex_2(X63,X61)))|~m1_pre_topc(X62,X61)|(v2_struct_0(X61)|~l1_pre_topc(X61)))&((m1_subset_1(esk3_2(X61,X62),k1_zfmisc_1(u1_struct_0(X61)))|v4_tex_2(X62,X61)|~m1_pre_topc(X62,X61)|(v2_struct_0(X61)|~l1_pre_topc(X61)))&((esk3_2(X61,X62)=u1_struct_0(X62)|v4_tex_2(X62,X61)|~m1_pre_topc(X62,X61)|(v2_struct_0(X61)|~l1_pre_topc(X61)))&(~v3_tex_2(esk3_2(X61,X62),X61)|v4_tex_2(X62,X61)|~m1_pre_topc(X62,X61)|(v2_struct_0(X61)|~l1_pre_topc(X61)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tex_2])])])])])])).
% 0.18/0.39  fof(c_0_20, plain, ![X59, X60]:(~l1_pre_topc(X59)|(~m1_pre_topc(X60,X59)|m1_subset_1(u1_struct_0(X60),k1_zfmisc_1(u1_struct_0(X59))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.18/0.39  fof(c_0_21, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_tex_2(X2,X1))&m1_pre_topc(X2,X1))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_borsuk_1(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(X4=X5=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k6_domain_1(u1_struct_0(X2),X4))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X5)))))))))), inference(assume_negation,[status(cth)],[t77_tex_2])).
% 0.18/0.39  fof(c_0_22, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.18/0.39  fof(c_0_23, plain, ![X12, X13, X14, X15, X16]:((~r1_tarski(X12,X13)|(~r2_hidden(X14,X12)|r2_hidden(X14,X13)))&((r2_hidden(esk2_2(X15,X16),X15)|r1_tarski(X15,X16))&(~r2_hidden(esk2_2(X15,X16),X16)|r1_tarski(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.39  fof(c_0_24, plain, ![X54, X55]:(v1_xboole_0(X54)|~m1_subset_1(X55,X54)|k6_domain_1(X54,X55)=k1_tarski(X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.18/0.39  fof(c_0_25, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.39  fof(c_0_26, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.39  fof(c_0_27, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.39  fof(c_0_28, plain, ![X24, X25, X26, X27]:k3_enumset1(X24,X24,X25,X26,X27)=k2_enumset1(X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.39  fof(c_0_29, plain, ![X28, X29, X30, X31, X32]:k4_enumset1(X28,X28,X29,X30,X31,X32)=k3_enumset1(X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.18/0.39  fof(c_0_30, plain, ![X33, X34, X35, X36, X37, X38]:k5_enumset1(X33,X33,X34,X35,X36,X37,X38)=k4_enumset1(X33,X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.18/0.39  fof(c_0_31, plain, ![X39, X40, X41, X42, X43, X44, X45]:k6_enumset1(X39,X39,X40,X41,X42,X43,X44,X45)=k5_enumset1(X39,X40,X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.18/0.39  cnf(c_0_32, plain, (v3_tex_2(X3,X2)|v2_struct_0(X2)|~v4_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.39  cnf(c_0_33, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.39  fof(c_0_34, negated_conjecture, ((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v3_tdlat_3(esk4_0))&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v4_tex_2(esk5_0,esk4_0))&m1_pre_topc(esk5_0,esk4_0))&((((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)))&v5_pre_topc(esk6_0,esk4_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))))&(v3_borsuk_1(esk6_0,esk4_0,esk5_0)&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&(m1_subset_1(esk8_0,u1_struct_0(esk4_0))&(esk7_0=esk8_0&k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0))!=k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk8_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.18/0.39  fof(c_0_35, plain, ![X46, X47]:((~m1_subset_1(X46,k1_zfmisc_1(X47))|r1_tarski(X46,X47))&(~r1_tarski(X46,X47)|m1_subset_1(X46,k1_zfmisc_1(X47)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.39  cnf(c_0_36, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.39  cnf(c_0_37, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.39  cnf(c_0_38, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.39  cnf(c_0_39, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.39  cnf(c_0_40, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.39  cnf(c_0_41, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.39  cnf(c_0_42, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.39  cnf(c_0_43, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.39  cnf(c_0_44, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.39  cnf(c_0_45, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.39  fof(c_0_46, plain, ![X65, X66]:(v2_struct_0(X65)|~v2_pre_topc(X65)|~l1_pre_topc(X65)|(~v1_xboole_0(X66)|~m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))|~v3_tex_2(X66,X65))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_tex_2])])])])).
% 0.18/0.39  cnf(c_0_47, plain, (v3_tex_2(u1_struct_0(X1),X2)|v2_struct_0(X2)|~v4_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_33])).
% 0.18/0.39  cnf(c_0_48, negated_conjecture, (v4_tex_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_49, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_51, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_52, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.39  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.39  fof(c_0_54, plain, ![X56, X57, X58]:(v1_xboole_0(X56)|~m1_subset_1(X57,X56)|~m1_subset_1(X58,X56)|k7_domain_1(X56,X57,X58)=k2_tarski(X57,X58)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).
% 0.18/0.39  cnf(c_0_55, plain, (k6_domain_1(X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 0.18/0.39  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_57, plain, (v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.39  cnf(c_0_58, negated_conjecture, (v3_tex_2(u1_struct_0(esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50])]), c_0_51])).
% 0.18/0.39  cnf(c_0_59, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_60, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.18/0.39  cnf(c_0_61, plain, (v1_xboole_0(X1)|k7_domain_1(X1,X2,X3)=k2_tarski(X2,X3)|~m1_subset_1(X2,X1)|~m1_subset_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.18/0.39  cnf(c_0_62, negated_conjecture, (k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)=k6_domain_1(u1_struct_0(esk5_0),esk7_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.18/0.39  cnf(c_0_63, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_50])]), c_0_51]), c_0_60])).
% 0.18/0.39  fof(c_0_64, plain, ![X67, X68, X69, X70, X71]:(v2_struct_0(X67)|~v2_pre_topc(X67)|~v3_tdlat_3(X67)|~l1_pre_topc(X67)|(v2_struct_0(X68)|~v4_tex_2(X68,X67)|~m1_pre_topc(X68,X67)|(~v1_funct_1(X69)|~v1_funct_2(X69,u1_struct_0(X67),u1_struct_0(X68))|~v5_pre_topc(X69,X67,X68)|~m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X67),u1_struct_0(X68))))|(~v3_borsuk_1(X69,X67,X68)|(~m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X68)))|(~m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X67)))|(X70!=X71|k8_relset_1(u1_struct_0(X67),u1_struct_0(X68),X69,X70)=k2_pre_topc(X67,X71)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t76_tex_2])])])])).
% 0.18/0.39  fof(c_0_65, plain, ![X48, X49, X50]:(~l1_pre_topc(X48)|(~m1_pre_topc(X49,X48)|(~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))|m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.18/0.39  cnf(c_0_66, plain, (k7_domain_1(X1,X2,X3)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)|v1_xboole_0(X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 0.18/0.39  cnf(c_0_67, negated_conjecture, (k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)=k6_domain_1(u1_struct_0(esk5_0),esk7_0)), inference(sr,[status(thm)],[c_0_62, c_0_63])).
% 0.18/0.39  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_69, negated_conjecture, (esk7_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_70, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.39  cnf(c_0_71, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.39  cnf(c_0_72, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k2_pre_topc(X1,X5)|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~v4_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v5_pre_topc(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v3_borsuk_1(X3,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))|X4!=X5), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.18/0.39  cnf(c_0_73, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.18/0.39  fof(c_0_74, plain, ![X51, X52, X53]:(v1_xboole_0(X51)|~m1_subset_1(X52,X51)|~m1_subset_1(X53,X51)|m1_subset_1(k7_domain_1(X51,X52,X53),k1_zfmisc_1(X51))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_domain_1])])])).
% 0.18/0.39  cnf(c_0_75, negated_conjecture, (k7_domain_1(X1,esk7_0,esk7_0)=k6_domain_1(u1_struct_0(esk5_0),esk7_0)|v1_xboole_0(X1)|~m1_subset_1(esk7_0,X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.18/0.39  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.18/0.39  cnf(c_0_77, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.18/0.39  cnf(c_0_78, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0))!=k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk8_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_79, plain, (k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k2_pre_topc(X1,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~v3_borsuk_1(X3,X1,X2)|~v5_pre_topc(X3,X1,X2)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)|~v4_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_72]), c_0_73])).
% 0.18/0.39  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_81, negated_conjecture, (v3_borsuk_1(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_82, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_83, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_84, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_85, negated_conjecture, (v3_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_86, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_87, plain, (v1_xboole_0(X1)|m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)|~m1_subset_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.18/0.39  cnf(c_0_88, negated_conjecture, (k7_domain_1(u1_struct_0(esk5_0),esk7_0,esk7_0)=k6_domain_1(u1_struct_0(esk5_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_56]), c_0_63])).
% 0.18/0.39  cnf(c_0_89, negated_conjecture, (k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)=k6_domain_1(u1_struct_0(esk4_0),esk7_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_76])).
% 0.18/0.39  cnf(c_0_90, plain, (r2_hidden(X1,u1_struct_0(X2))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_struct_0(X3))), inference(spm,[status(thm)],[c_0_77, c_0_33])).
% 0.18/0.39  cnf(c_0_91, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.39  cnf(c_0_92, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0))!=k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk7_0))), inference(rw,[status(thm)],[c_0_78, c_0_69])).
% 0.18/0.39  cnf(c_0_93, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)=k2_pre_topc(esk4_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), c_0_82]), c_0_83]), c_0_84]), c_0_85]), c_0_59]), c_0_48]), c_0_49]), c_0_50])]), c_0_51]), c_0_86])).
% 0.18/0.39  cnf(c_0_94, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_56])]), c_0_63])).
% 0.18/0.39  cnf(c_0_95, negated_conjecture, (k6_domain_1(u1_struct_0(esk5_0),esk7_0)=k6_domain_1(u1_struct_0(esk4_0),esk7_0)|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_62, c_0_89])).
% 0.18/0.39  cnf(c_0_96, plain, (r2_hidden(esk1_1(u1_struct_0(X1)),u1_struct_0(X2))|v1_xboole_0(u1_struct_0(X1))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.18/0.39  cnf(c_0_97, negated_conjecture, (k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0))!=k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])])).
% 0.18/0.39  cnf(c_0_98, negated_conjecture, (k6_domain_1(u1_struct_0(esk5_0),esk7_0)=k6_domain_1(u1_struct_0(esk4_0),esk7_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[c_0_95, c_0_63])).
% 0.18/0.39  cnf(c_0_99, negated_conjecture, (r2_hidden(esk1_1(u1_struct_0(esk5_0)),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_49]), c_0_50])]), c_0_63])).
% 0.18/0.39  cnf(c_0_100, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.18/0.39  cnf(c_0_101, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_99]), c_0_100])]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 102
% 0.18/0.39  # Proof object clause steps            : 63
% 0.18/0.39  # Proof object formula steps           : 39
% 0.18/0.39  # Proof object conjectures             : 36
% 0.18/0.39  # Proof object clause conjectures      : 33
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 37
% 0.18/0.39  # Proof object initial formulas used   : 19
% 0.18/0.39  # Proof object generating inferences   : 18
% 0.18/0.39  # Proof object simplifying inferences  : 53
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 19
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 41
% 0.18/0.39  # Removed in clause preprocessing      : 7
% 0.18/0.39  # Initial clauses in saturation        : 34
% 0.18/0.39  # Processed clauses                    : 250
% 0.18/0.39  # ...of these trivial                  : 2
% 0.18/0.39  # ...subsumed                          : 33
% 0.18/0.39  # ...remaining for further processing  : 215
% 0.18/0.39  # Other redundant clauses eliminated   : 2
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 17
% 0.18/0.39  # Backward-rewritten                   : 22
% 0.18/0.39  # Generated clauses                    : 546
% 0.18/0.39  # ...of the previous two non-trivial   : 521
% 0.18/0.39  # Contextual simplify-reflections      : 3
% 0.18/0.39  # Paramodulations                      : 542
% 0.18/0.39  # Factorizations                       : 0
% 0.18/0.39  # Equation resolutions                 : 2
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.40  #    Success case prop solver time     : 0.000
% 0.18/0.40  # Current number of processed clauses  : 138
% 0.18/0.40  #    Positive orientable unit clauses  : 26
% 0.18/0.40  #    Positive unorientable unit clauses: 0
% 0.18/0.40  #    Negative unit clauses             : 5
% 0.18/0.40  #    Non-unit-clauses                  : 107
% 0.18/0.40  # Current number of unprocessed clauses: 298
% 0.18/0.40  # ...number of literals in the above   : 1103
% 0.18/0.40  # Current number of archived formulas  : 0
% 0.18/0.40  # Current number of archived clauses   : 82
% 0.18/0.40  # Clause-clause subsumption calls (NU) : 2195
% 0.18/0.40  # Rec. Clause-clause subsumption calls : 836
% 0.18/0.40  # Non-unit clause-clause subsumptions  : 51
% 0.18/0.40  # Unit Clause-clause subsumption calls : 95
% 0.18/0.40  # Rewrite failures with RHS unbound    : 0
% 0.18/0.40  # BW rewrite match attempts            : 17
% 0.18/0.40  # BW rewrite match successes           : 9
% 0.18/0.40  # Condensation attempts                : 0
% 0.18/0.40  # Condensation successes               : 0
% 0.18/0.40  # Termbank termtop insertions          : 22496
% 0.18/0.40  
% 0.18/0.40  # -------------------------------------------------
% 0.18/0.40  # User time                : 0.052 s
% 0.18/0.40  # System time              : 0.008 s
% 0.18/0.40  # Total time               : 0.059 s
% 0.18/0.40  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
