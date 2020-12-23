%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1869+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:56 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :  141 (5114 expanded)
%              Number of clauses        :  102 (1796 expanded)
%              Number of leaves         :   19 (1206 expanded)
%              Depth                    :   27
%              Number of atoms          :  530 (39769 expanded)
%              Number of equality atoms :   51 (3214 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   61 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = k6_domain_1(u1_struct_0(X1),X3) ) ) ) )
           => v2_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tex_2)).

fof(t10_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ? [X3] :
              ( ~ v2_struct_0(X3)
              & v1_pre_topc(X3)
              & m1_pre_topc(X3,X1)
              & X2 = u1_struct_0(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

fof(t35_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => v2_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(t26_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v2_tex_2(X3,X1)
                <=> v1_tdlat_3(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t19_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( X2 = k1_tarski(X3)
                 => v3_pre_topc(X2,X1) ) ) )
       => v1_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tdlat_3)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(d9_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X2,X1)
          <=> ( r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( r2_hidden(X3,u1_pre_topc(X2))
                  <=> ? [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X4,u1_pre_topc(X1))
                        & X3 = k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ~ ( r2_hidden(X3,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( v3_pre_topc(X4,X1)
                              & k9_subset_1(u1_struct_0(X1),X2,X4) = k6_domain_1(u1_struct_0(X1),X3) ) ) ) )
             => v2_tex_2(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_tex_2])).

fof(c_0_20,plain,(
    ! [X36,X37] :
      ( ( ~ v2_struct_0(esk4_2(X36,X37))
        | v1_xboole_0(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ l1_pre_topc(X36) )
      & ( v1_pre_topc(esk4_2(X36,X37))
        | v1_xboole_0(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ l1_pre_topc(X36) )
      & ( m1_pre_topc(esk4_2(X36,X37),X36)
        | v1_xboole_0(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ l1_pre_topc(X36) )
      & ( X37 = u1_struct_0(esk4_2(X36,X37))
        | v1_xboole_0(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).

fof(c_0_21,negated_conjecture,(
    ! [X54] :
      ( ~ v2_struct_0(esk7_0)
      & v2_pre_topc(esk7_0)
      & l1_pre_topc(esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
      & ( m1_subset_1(esk9_1(X54),k1_zfmisc_1(u1_struct_0(esk7_0)))
        | ~ r2_hidden(X54,esk8_0)
        | ~ m1_subset_1(X54,u1_struct_0(esk7_0)) )
      & ( v3_pre_topc(esk9_1(X54),esk7_0)
        | ~ r2_hidden(X54,esk8_0)
        | ~ m1_subset_1(X54,u1_struct_0(esk7_0)) )
      & ( k9_subset_1(u1_struct_0(esk7_0),esk8_0,esk9_1(X54)) = k6_domain_1(u1_struct_0(esk7_0),X54)
        | ~ r2_hidden(X54,esk8_0)
        | ~ m1_subset_1(X54,u1_struct_0(esk7_0)) )
      & ~ v2_tex_2(esk8_0,esk7_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])])])).

cnf(c_0_22,plain,
    ( X1 = u1_struct_0(esk4_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( m1_pre_topc(esk4_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X47,X48] :
      ( v2_struct_0(X47)
      | ~ v2_pre_topc(X47)
      | ~ l1_pre_topc(X47)
      | ~ v1_xboole_0(X48)
      | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
      | v2_tex_2(X48,X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_tex_2])])])])).

cnf(c_0_27,negated_conjecture,
    ( u1_struct_0(esk4_2(esk7_0,X1)) = X1
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v1_xboole_0(X1)
    | m1_pre_topc(esk4_2(esk7_0,X1),esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_24])).

fof(c_0_30,plain,(
    ! [X42,X43,X44] :
      ( ( ~ v2_tex_2(X44,X42)
        | v1_tdlat_3(X43)
        | X44 != u1_struct_0(X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
        | v2_struct_0(X43)
        | ~ m1_pre_topc(X43,X42)
        | v2_struct_0(X42)
        | ~ l1_pre_topc(X42) )
      & ( ~ v1_tdlat_3(X43)
        | v2_tex_2(X44,X42)
        | X44 != u1_struct_0(X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
        | v2_struct_0(X43)
        | ~ m1_pre_topc(X43,X42)
        | v2_struct_0(X42)
        | ~ l1_pre_topc(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(esk4_2(esk7_0,esk8_0)) = esk8_0
    | v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_33,plain,(
    ! [X28,X29] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_pre_topc(X29,X28)
      | l1_pre_topc(X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_34,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | m1_pre_topc(esk4_2(esk7_0,esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

fof(c_0_35,plain,(
    ! [X5,X6] :
      ( ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(X6,X5)
      | v2_pre_topc(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_36,plain,
    ( v2_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( u1_struct_0(esk4_2(esk7_0,esk8_0)) = esk8_0
    | v2_tex_2(esk8_0,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_tex_2(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( v2_tex_2(esk8_0,X1)
    | v2_struct_0(X1)
    | m1_pre_topc(esk4_2(esk7_0,esk8_0),esk7_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_34])).

cnf(c_0_42,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( v2_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(esk4_2(esk7_0,esk8_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_23]),c_0_28]),c_0_38])]),c_0_39]),c_0_24])).

fof(c_0_45,plain,(
    ! [X39] :
      ( ( m1_subset_1(esk5_1(X39),k1_zfmisc_1(u1_struct_0(X39)))
        | v1_tdlat_3(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( m1_subset_1(esk6_1(X39),u1_struct_0(X39))
        | v1_tdlat_3(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( esk5_1(X39) = k1_tarski(esk6_1(X39))
        | v1_tdlat_3(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( ~ v3_pre_topc(esk5_1(X39),X39)
        | v1_tdlat_3(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_tdlat_3])])])])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(esk4_2(esk7_0,esk8_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_23]),c_0_28]),c_0_38])]),c_0_39]),c_0_24])).

cnf(c_0_48,negated_conjecture,
    ( v2_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_23]),c_0_38])])).

cnf(c_0_49,negated_conjecture,
    ( v2_tex_2(esk8_0,X1)
    | v2_struct_0(esk4_2(esk7_0,esk8_0))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(esk4_2(esk7_0,esk8_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk4_2(esk7_0,esk8_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk6_1(X1),u1_struct_0(X1))
    | v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( l1_pre_topc(esk4_2(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( v2_pre_topc(esk4_2(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk4_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_54,negated_conjecture,
    ( v2_struct_0(esk4_2(esk7_0,esk8_0))
    | ~ v1_tdlat_3(esk4_2(esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_23]),c_0_28]),c_0_47])]),c_0_39]),c_0_24])).

cnf(c_0_55,negated_conjecture,
    ( v1_tdlat_3(esk4_2(esk7_0,esk8_0))
    | m1_subset_1(esk6_1(esk4_2(esk7_0,esk8_0)),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_44]),c_0_52])])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(esk4_2(esk7_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_23]),c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(esk4_2(esk7_0,esk8_0))
    | m1_subset_1(esk6_1(esk4_2(esk7_0,esk8_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | m1_subset_1(esk6_1(esk4_2(esk7_0,esk8_0)),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_28])])).

fof(c_0_59,plain,(
    ! [X27] :
      ( ~ l1_pre_topc(X27)
      | l1_struct_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_60,plain,(
    ! [X45,X46] :
      ( ~ m1_subset_1(X45,X46)
      | v1_xboole_0(X46)
      | r2_hidden(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_61,negated_conjecture,
    ( v2_tex_2(esk8_0,X1)
    | v2_struct_0(X1)
    | m1_subset_1(esk6_1(esk4_2(esk7_0,esk8_0)),esk8_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_58])).

fof(c_0_62,plain,(
    ! [X12] :
      ( ~ l1_struct_0(X12)
      | k2_struct_0(X12) = u1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_63,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk6_1(esk4_2(esk7_0,esk8_0)),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_23]),c_0_28]),c_0_38])]),c_0_39]),c_0_24])).

fof(c_0_66,plain,(
    ! [X23] :
      ( ~ l1_struct_0(X23)
      | m1_subset_1(k2_struct_0(X23),k1_zfmisc_1(u1_struct_0(X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_67,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( l1_struct_0(esk4_2(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_51])).

cnf(c_0_69,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | r2_hidden(esk6_1(esk4_2(esk7_0,esk8_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( k2_struct_0(esk4_2(esk7_0,esk8_0)) = u1_struct_0(esk4_2(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

fof(c_0_72,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(X33))
      | k9_subset_1(X33,X34,X35) = k3_xboole_0(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_73,plain,
    ( m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_74,plain,(
    ! [X49,X50,X51] :
      ( ~ r2_hidden(X49,X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(X51))
      | m1_subset_1(X49,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_75,negated_conjecture,
    ( v2_tex_2(esk8_0,X1)
    | v2_struct_0(X1)
    | r2_hidden(esk6_1(esk4_2(esk7_0,esk8_0)),esk8_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_69])).

fof(c_0_76,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X9))
      | k9_subset_1(X9,X10,X11) = k9_subset_1(X9,X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_2(esk7_0,esk8_0)),k1_zfmisc_1(u1_struct_0(esk4_2(esk7_0,esk8_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_68])])).

cnf(c_0_78,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,plain,
    ( esk5_1(X1) = k1_tarski(esk6_1(X1))
    | v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_80,negated_conjecture,
    ( v1_tdlat_3(esk4_2(esk7_0,esk8_0))
    | m1_subset_1(esk5_1(esk4_2(esk7_0,esk8_0)),k1_zfmisc_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_51]),c_0_44]),c_0_52])])).

fof(c_0_81,plain,(
    ! [X15,X16,X17,X19,X21] :
      ( ( r1_tarski(k2_struct_0(X16),k2_struct_0(X15))
        | ~ m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk1_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X15)))
        | ~ r2_hidden(X17,u1_pre_topc(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(esk1_3(X15,X16,X17),u1_pre_topc(X15))
        | ~ r2_hidden(X17,u1_pre_topc(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( X17 = k9_subset_1(u1_struct_0(X16),esk1_3(X15,X16,X17),k2_struct_0(X16))
        | ~ r2_hidden(X17,u1_pre_topc(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ r2_hidden(X19,u1_pre_topc(X15))
        | X17 != k9_subset_1(u1_struct_0(X16),X19,k2_struct_0(X16))
        | r2_hidden(X17,u1_pre_topc(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk2_2(X15,X16),k1_zfmisc_1(u1_struct_0(X16)))
        | ~ r1_tarski(k2_struct_0(X16),k2_struct_0(X15))
        | m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( ~ r2_hidden(esk2_2(X15,X16),u1_pre_topc(X16))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ r2_hidden(X21,u1_pre_topc(X15))
        | esk2_2(X15,X16) != k9_subset_1(u1_struct_0(X16),X21,k2_struct_0(X16))
        | ~ r1_tarski(k2_struct_0(X16),k2_struct_0(X15))
        | m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk3_2(X15,X16),k1_zfmisc_1(u1_struct_0(X15)))
        | r2_hidden(esk2_2(X15,X16),u1_pre_topc(X16))
        | ~ r1_tarski(k2_struct_0(X16),k2_struct_0(X15))
        | m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(esk3_2(X15,X16),u1_pre_topc(X15))
        | r2_hidden(esk2_2(X15,X16),u1_pre_topc(X16))
        | ~ r1_tarski(k2_struct_0(X16),k2_struct_0(X15))
        | m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( esk2_2(X15,X16) = k9_subset_1(u1_struct_0(X16),esk3_2(X15,X16),k2_struct_0(X16))
        | r2_hidden(esk2_2(X15,X16),u1_pre_topc(X16))
        | ~ r1_tarski(k2_struct_0(X16),k2_struct_0(X15))
        | m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_82,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X24))
      | m1_subset_1(k9_subset_1(X24,X25,X26),k1_zfmisc_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_83,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk6_1(esk4_2(esk7_0,esk8_0)),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_23]),c_0_28]),c_0_38])]),c_0_39]),c_0_24])).

cnf(c_0_85,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_44]),c_0_44])).

cnf(c_0_87,negated_conjecture,
    ( k3_xboole_0(X1,esk8_0) = k9_subset_1(u1_struct_0(esk7_0),X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_28])).

fof(c_0_88,plain,(
    ! [X30] :
      ( v2_struct_0(X30)
      | ~ l1_struct_0(X30)
      | ~ v1_xboole_0(u1_struct_0(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_89,negated_conjecture,
    ( k1_tarski(esk6_1(esk4_2(esk7_0,esk8_0))) = esk5_1(esk4_2(esk7_0,esk8_0))
    | v1_tdlat_3(esk4_2(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_51]),c_0_52])])).

fof(c_0_90,plain,(
    ! [X13,X14] :
      ( ( ~ v3_pre_topc(X14,X13)
        | r2_hidden(X14,u1_pre_topc(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(X14,u1_pre_topc(X13))
        | v3_pre_topc(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_91,negated_conjecture,
    ( v2_struct_0(esk4_2(esk7_0,esk8_0))
    | m1_subset_1(esk5_1(esk4_2(esk7_0,esk8_0)),k1_zfmisc_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_80])).

cnf(c_0_92,plain,
    ( r2_hidden(X3,u1_pre_topc(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | X3 != k9_subset_1(u1_struct_0(X4),X1,k2_struct_0(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_93,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk6_1(esk4_2(esk7_0,esk8_0)),X1)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_95,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk7_0),esk8_0,X1) = k9_subset_1(u1_struct_0(esk7_0),X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_28])).

cnf(c_0_96,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk7_0),X1,esk8_0) = k9_subset_1(esk8_0,X1,esk8_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_86]),c_0_87])).

fof(c_0_97,plain,(
    ! [X31,X32] :
      ( v1_xboole_0(X31)
      | ~ m1_subset_1(X32,X31)
      | k6_domain_1(X31,X32) = k1_tarski(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_98,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_99,negated_conjecture,
    ( l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_23])).

cnf(c_0_100,negated_conjecture,
    ( k1_tarski(esk6_1(esk4_2(esk7_0,esk8_0))) = esk5_1(esk4_2(esk7_0,esk8_0))
    | v2_struct_0(esk4_2(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_89])).

cnf(c_0_101,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_102,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | m1_subset_1(esk5_1(esk4_2(esk7_0,esk8_0)),k1_zfmisc_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_91]),c_0_28])])).

cnf(c_0_103,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_92,c_0_40])])).

cnf(c_0_104,negated_conjecture,
    ( k2_struct_0(esk4_2(esk7_0,esk8_0)) = esk8_0 ),
    inference(rw,[status(thm)],[c_0_71,c_0_44])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(k9_subset_1(esk8_0,X1,esk8_0),k1_zfmisc_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_86])).

cnf(c_0_106,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_107,negated_conjecture,
    ( v3_pre_topc(esk9_1(X1),esk7_0)
    | ~ r2_hidden(X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(esk6_1(esk4_2(esk7_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_28])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(esk9_1(X1),k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_110,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk7_0),esk8_0,esk9_1(X1)) = k6_domain_1(u1_struct_0(esk7_0),X1)
    | ~ r2_hidden(X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_111,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk7_0),esk8_0,X1) = k9_subset_1(esk8_0,X1,esk8_0) ),
    inference(rw,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_112,negated_conjecture,
    ( k9_subset_1(esk8_0,esk8_0,X1) = k9_subset_1(esk8_0,X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_113,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_114,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_24])).

cnf(c_0_115,negated_conjecture,
    ( k1_tarski(esk6_1(esk4_2(esk7_0,esk8_0))) = esk5_1(esk4_2(esk7_0,esk8_0))
    | v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_100]),c_0_28])])).

cnf(c_0_116,negated_conjecture,
    ( v3_pre_topc(X1,esk4_2(esk7_0,esk8_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk4_2(esk7_0,esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_2(esk7_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_101,c_0_51])).

cnf(c_0_117,negated_conjecture,
    ( v2_tex_2(esk8_0,X1)
    | v2_struct_0(X1)
    | m1_subset_1(esk5_1(esk4_2(esk7_0,esk8_0)),k1_zfmisc_1(esk8_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_102])).

cnf(c_0_118,negated_conjecture,
    ( r2_hidden(k9_subset_1(esk8_0,X1,esk8_0),u1_pre_topc(esk4_2(esk7_0,esk8_0)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(esk4_2(esk7_0,esk8_0),X2)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_44]),c_0_44]),c_0_44]),c_0_105])])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk7_0))
    | ~ v3_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_106,c_0_23])).

cnf(c_0_120,negated_conjecture,
    ( v3_pre_topc(esk9_1(esk6_1(esk4_2(esk7_0,esk8_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_84]),c_0_108])])).

cnf(c_0_121,negated_conjecture,
    ( m1_subset_1(esk9_1(esk6_1(esk4_2(esk7_0,esk8_0))),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_84]),c_0_108])])).

cnf(c_0_122,negated_conjecture,
    ( k9_subset_1(esk8_0,esk8_0,esk9_1(X1)) = k6_domain_1(u1_struct_0(esk7_0),X1)
    | ~ r2_hidden(X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111]),c_0_112])).

cnf(c_0_123,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk7_0),esk6_1(esk4_2(esk7_0,esk8_0))) = k1_tarski(esk6_1(esk4_2(esk7_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_108]),c_0_114])).

cnf(c_0_124,negated_conjecture,
    ( k1_tarski(esk6_1(esk4_2(esk7_0,esk8_0))) = esk5_1(esk4_2(esk7_0,esk8_0))
    | v2_tex_2(esk8_0,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_115])).

cnf(c_0_125,negated_conjecture,
    ( v3_pre_topc(X1,esk4_2(esk7_0,esk8_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk4_2(esk7_0,esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_116,c_0_44])).

cnf(c_0_126,negated_conjecture,
    ( m1_subset_1(esk5_1(esk4_2(esk7_0,esk8_0)),k1_zfmisc_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_23]),c_0_28]),c_0_38])]),c_0_39]),c_0_24])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(k9_subset_1(esk8_0,X1,esk8_0),u1_pre_topc(esk4_2(esk7_0,esk8_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_23]),c_0_47])])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(esk9_1(esk6_1(esk4_2(esk7_0,esk8_0))),u1_pre_topc(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_121])])).

cnf(c_0_129,negated_conjecture,
    ( k9_subset_1(esk8_0,esk8_0,esk9_1(esk6_1(esk4_2(esk7_0,esk8_0)))) = k1_tarski(esk6_1(esk4_2(esk7_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_84]),c_0_123]),c_0_108])])).

cnf(c_0_130,negated_conjecture,
    ( k1_tarski(esk6_1(esk4_2(esk7_0,esk8_0))) = esk5_1(esk4_2(esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_23]),c_0_28]),c_0_38])]),c_0_39]),c_0_24])).

cnf(c_0_131,plain,
    ( v1_tdlat_3(X1)
    | ~ v3_pre_topc(esk5_1(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_132,negated_conjecture,
    ( v3_pre_topc(esk5_1(esk4_2(esk7_0,esk8_0)),esk4_2(esk7_0,esk8_0))
    | ~ r2_hidden(esk5_1(esk4_2(esk7_0,esk8_0)),u1_pre_topc(esk4_2(esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(esk5_1(esk4_2(esk7_0,esk8_0)),u1_pre_topc(esk4_2(esk7_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_112]),c_0_129]),c_0_130]),c_0_121])])).

cnf(c_0_134,negated_conjecture,
    ( v1_tdlat_3(esk4_2(esk7_0,esk8_0))
    | ~ v3_pre_topc(esk5_1(esk4_2(esk7_0,esk8_0)),esk4_2(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_51]),c_0_52])])).

cnf(c_0_135,negated_conjecture,
    ( v3_pre_topc(esk5_1(esk4_2(esk7_0,esk8_0)),esk4_2(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_133])])).

cnf(c_0_136,negated_conjecture,
    ( v1_tdlat_3(esk4_2(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_135])])).

cnf(c_0_137,negated_conjecture,
    ( v2_struct_0(esk4_2(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_136])])).

cnf(c_0_138,negated_conjecture,
    ( v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_137]),c_0_28])])).

cnf(c_0_139,negated_conjecture,
    ( v2_tex_2(esk8_0,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_138])).

cnf(c_0_140,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_23]),c_0_28]),c_0_38])]),c_0_39]),c_0_24]),
    [proof]).

%------------------------------------------------------------------------------
