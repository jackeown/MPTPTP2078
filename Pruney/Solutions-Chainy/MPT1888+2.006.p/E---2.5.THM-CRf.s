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
% DateTime   : Thu Dec  3 11:20:45 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 462 expanded)
%              Number of clauses        :   51 ( 184 expanded)
%              Number of leaves         :   15 ( 113 expanded)
%              Depth                    :   13
%              Number of atoms          :  266 (1910 expanded)
%              Number of equality atoms :   43 ( 253 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t56_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))
                | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(projectivity_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(t24_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

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

fof(t40_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r1_xboole_0(X2,X3)
                  & v3_pre_topc(X2,X1) )
               => r1_xboole_0(X2,k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tsep_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t55_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))
               => k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))
                  | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t56_tex_2])).

fof(c_0_16,plain,(
    ! [X28] :
      ( ~ l1_pre_topc(X28)
      | l1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & v3_tdlat_3(esk5_0)
    & l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & ~ r1_xboole_0(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0)))
    & k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)) != k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X29] :
      ( v2_struct_0(X29)
      | ~ l1_struct_0(X29)
      | ~ v1_xboole_0(u1_struct_0(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_19,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | m1_subset_1(k1_tarski(X22),k1_zfmisc_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

fof(c_0_22,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X24,X25)
      | v1_xboole_0(X25)
      | r2_hidden(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X34,X35] :
      ( v1_xboole_0(X34)
      | ~ m1_subset_1(X35,X34)
      | k6_domain_1(X34,X35) = k1_tarski(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_28,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | m1_subset_1(k2_pre_topc(X26,X27),k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_35,plain,
    ( m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_37,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_33,c_0_29])).

fof(c_0_38,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X14
        | X15 != k1_tarski(X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k1_tarski(X14) )
      & ( ~ r2_hidden(esk3_2(X18,X19),X19)
        | esk3_2(X18,X19) != X18
        | X19 = k1_tarski(X18) )
      & ( r2_hidden(esk3_2(X18,X19),X19)
        | esk3_2(X18,X19) = X18
        | X19 = k1_tarski(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_42,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | k2_pre_topc(X30,k2_pre_topc(X30,X31)) = k2_pre_topc(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).

cnf(c_0_43,negated_conjecture,
    ( k2_tarski(esk6_0,esk6_0) = k6_domain_1(u1_struct_0(esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_32])).

cnf(c_0_44,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_39]),c_0_32])).

fof(c_0_46,plain,(
    ! [X36,X37] :
      ( ( ~ v3_tdlat_3(X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v4_pre_topc(X37,X36)
        | v3_pre_topc(X37,X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( m1_subset_1(esk4_1(X36),k1_zfmisc_1(u1_struct_0(X36)))
        | v3_tdlat_3(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( v4_pre_topc(esk4_1(X36),X36)
        | v3_tdlat_3(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( ~ v3_pre_topc(esk4_1(X36),X36)
        | v3_tdlat_3(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk5_0,k2_tarski(esk6_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_20])])).

fof(c_0_48,plain,(
    ! [X32,X33] :
      ( ( ~ v4_pre_topc(X33,X32)
        | k2_pre_topc(X32,X33) = X33
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_pre_topc(X32) )
      & ( ~ v2_pre_topc(X32)
        | k2_pre_topc(X32,X33) != X33
        | v4_pre_topc(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_49,plain,
    ( k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_43])).

cnf(c_0_51,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_29])).

fof(c_0_52,plain,(
    ! [X39,X40,X41] :
      ( ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))
      | ~ r1_xboole_0(X40,X41)
      | ~ v3_pre_topc(X40,X39)
      | r1_xboole_0(X40,k2_pre_topc(X39,X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_tsep_1])])])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k2_tarski(esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k2_tarski(esk7_0,esk7_0) = k6_domain_1(u1_struct_0(esk5_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_39]),c_0_32])).

cnf(c_0_55,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_47,c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( v3_tdlat_3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_59,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X2) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( k2_pre_topc(esk5_0,k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))) = k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_20])])).

cnf(c_0_61,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_51])).

fof(c_0_62,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk2_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk2_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_63,plain,(
    ! [X42,X43,X44] :
      ( v2_struct_0(X42)
      | ~ v2_pre_topc(X42)
      | ~ v3_tdlat_3(X42)
      | ~ l1_pre_topc(X42)
      | ~ m1_subset_1(X43,u1_struct_0(X42))
      | ~ m1_subset_1(X44,u1_struct_0(X42))
      | ~ r2_hidden(X43,k2_pre_topc(X42,k6_domain_1(u1_struct_0(X42),X44)))
      | k2_pre_topc(X42,k6_domain_1(u1_struct_0(X42),X43)) = k2_pre_topc(X42,k6_domain_1(u1_struct_0(X42),X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_tex_2])])])])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X2,k2_pre_topc(X1,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X2,X3)
    | ~ v3_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( v3_pre_topc(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),esk5_0)
    | ~ v4_pre_topc(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58]),c_0_20])])).

cnf(c_0_67,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_58]),c_0_20])]),c_0_56])])).

cnf(c_0_68,negated_conjecture,
    ( X1 = esk7_0
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk5_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_54])).

cnf(c_0_69,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(X1,k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0)))
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk5_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_58]),c_0_20])])).

cnf(c_0_72,negated_conjecture,
    ( v3_pre_topc(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_73,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_74,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( esk2_2(X1,k6_domain_1(u1_struct_0(esk5_0),esk7_0)) = esk7_0
    | r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk5_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),X1)) = k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_31]),c_0_57]),c_0_58]),c_0_20])]),c_0_26])).

cnf(c_0_77,negated_conjecture,
    ( k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)) != k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),k6_domain_1(u1_struct_0(esk5_0),esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_56]),c_0_72])]),c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk5_0),esk7_0))
    | r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_39]),c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.19/0.39  # and selection function SelectGrCQArEqFirst.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.029 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t56_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tex_2)).
% 0.19/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.39  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.19/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.39  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.39  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.19/0.39  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.39  fof(projectivity_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 0.19/0.39  fof(t24_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 0.19/0.39  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.19/0.39  fof(t40_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_xboole_0(X2,X3)&v3_pre_topc(X2,X1))=>r1_xboole_0(X2,k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_tsep_1)).
% 0.19/0.39  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.39  fof(t55_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=>k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tex_2)).
% 0.19/0.39  fof(c_0_15, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))))))), inference(assume_negation,[status(cth)],[t56_tex_2])).
% 0.19/0.39  fof(c_0_16, plain, ![X28]:(~l1_pre_topc(X28)|l1_struct_0(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.39  fof(c_0_17, negated_conjecture, ((((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&v3_tdlat_3(esk5_0))&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&(~r1_xboole_0(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0)))&k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))!=k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.19/0.39  fof(c_0_18, plain, ![X29]:(v2_struct_0(X29)|~l1_struct_0(X29)|~v1_xboole_0(u1_struct_0(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.39  cnf(c_0_19, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  fof(c_0_21, plain, ![X22, X23]:(~r2_hidden(X22,X23)|m1_subset_1(k1_tarski(X22),k1_zfmisc_1(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.19/0.39  fof(c_0_22, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.39  fof(c_0_23, plain, ![X24, X25]:(~m1_subset_1(X24,X25)|(v1_xboole_0(X25)|r2_hidden(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.39  cnf(c_0_24, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  fof(c_0_27, plain, ![X34, X35]:(v1_xboole_0(X34)|~m1_subset_1(X35,X34)|k6_domain_1(X34,X35)=k1_tarski(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.39  cnf(c_0_28, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_30, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.19/0.39  cnf(c_0_33, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  fof(c_0_34, plain, ![X26, X27]:(~l1_pre_topc(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|m1_subset_1(k2_pre_topc(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.19/0.39  cnf(c_0_35, plain, (m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.39  cnf(c_0_36, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.19/0.39  cnf(c_0_37, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_33, c_0_29])).
% 0.19/0.39  fof(c_0_38, plain, ![X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X16,X15)|X16=X14|X15!=k1_tarski(X14))&(X17!=X14|r2_hidden(X17,X15)|X15!=k1_tarski(X14)))&((~r2_hidden(esk3_2(X18,X19),X19)|esk3_2(X18,X19)!=X18|X19=k1_tarski(X18))&(r2_hidden(esk3_2(X18,X19),X19)|esk3_2(X18,X19)=X18|X19=k1_tarski(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_40, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.39  fof(c_0_42, plain, ![X30, X31]:(~l1_pre_topc(X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|k2_pre_topc(X30,k2_pre_topc(X30,X31))=k2_pre_topc(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (k2_tarski(esk6_0,esk6_0)=k6_domain_1(u1_struct_0(esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_31]), c_0_32])).
% 0.19/0.39  cnf(c_0_44, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (r2_hidden(esk7_0,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_39]), c_0_32])).
% 0.19/0.39  fof(c_0_46, plain, ![X36, X37]:((~v3_tdlat_3(X36)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(~v4_pre_topc(X37,X36)|v3_pre_topc(X37,X36)))|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))&((m1_subset_1(esk4_1(X36),k1_zfmisc_1(u1_struct_0(X36)))|v3_tdlat_3(X36)|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))&((v4_pre_topc(esk4_1(X36),X36)|v3_tdlat_3(X36)|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(~v3_pre_topc(esk4_1(X36),X36)|v3_tdlat_3(X36)|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (m1_subset_1(k2_pre_topc(esk5_0,k2_tarski(esk6_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_20])])).
% 0.19/0.39  fof(c_0_48, plain, ![X32, X33]:((~v4_pre_topc(X33,X32)|k2_pre_topc(X32,X33)=X33|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_pre_topc(X32))&(~v2_pre_topc(X32)|k2_pre_topc(X32,X33)!=X33|v4_pre_topc(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_pre_topc(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.19/0.39  cnf(c_0_49, plain, (k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.39  cnf(c_0_50, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(rw,[status(thm)],[c_0_41, c_0_43])).
% 0.19/0.39  cnf(c_0_51, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_29])).
% 0.19/0.39  fof(c_0_52, plain, ![X39, X40, X41]:(~v2_pre_topc(X39)|~l1_pre_topc(X39)|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))|(~r1_xboole_0(X40,X41)|~v3_pre_topc(X40,X39)|r1_xboole_0(X40,k2_pre_topc(X39,X41)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_tsep_1])])])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (m1_subset_1(k2_tarski(esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_35, c_0_45])).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, (k2_tarski(esk7_0,esk7_0)=k6_domain_1(u1_struct_0(esk5_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_39]), c_0_32])).
% 0.19/0.39  cnf(c_0_55, plain, (v3_pre_topc(X2,X1)|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, (m1_subset_1(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(rw,[status(thm)],[c_0_47, c_0_43])).
% 0.19/0.39  cnf(c_0_57, negated_conjecture, (v3_tdlat_3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_58, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_59, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|k2_pre_topc(X1,X2)!=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, (k2_pre_topc(esk5_0,k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))=k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_20])])).
% 0.19/0.39  cnf(c_0_61, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_51])).
% 0.19/0.39  fof(c_0_62, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk2_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk2_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.39  fof(c_0_63, plain, ![X42, X43, X44]:(v2_struct_0(X42)|~v2_pre_topc(X42)|~v3_tdlat_3(X42)|~l1_pre_topc(X42)|(~m1_subset_1(X43,u1_struct_0(X42))|(~m1_subset_1(X44,u1_struct_0(X42))|(~r2_hidden(X43,k2_pre_topc(X42,k6_domain_1(u1_struct_0(X42),X44)))|k2_pre_topc(X42,k6_domain_1(u1_struct_0(X42),X43))=k2_pre_topc(X42,k6_domain_1(u1_struct_0(X42),X44)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_tex_2])])])])).
% 0.19/0.39  cnf(c_0_64, plain, (r1_xboole_0(X2,k2_pre_topc(X1,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_xboole_0(X2,X3)|~v3_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.39  cnf(c_0_65, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.39  cnf(c_0_66, negated_conjecture, (v3_pre_topc(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),esk5_0)|~v4_pre_topc(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58]), c_0_20])])).
% 0.19/0.39  cnf(c_0_67, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_58]), c_0_20])]), c_0_56])])).
% 0.19/0.39  cnf(c_0_68, negated_conjecture, (X1=esk7_0|~r2_hidden(X1,k6_domain_1(u1_struct_0(esk5_0),esk7_0))), inference(spm,[status(thm)],[c_0_61, c_0_54])).
% 0.19/0.39  cnf(c_0_69, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.39  cnf(c_0_70, plain, (v2_struct_0(X1)|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.39  cnf(c_0_71, negated_conjecture, (r1_xboole_0(X1,k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0)))|~v3_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk5_0),esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_58]), c_0_20])])).
% 0.19/0.39  cnf(c_0_72, negated_conjecture, (v3_pre_topc(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])])).
% 0.19/0.39  cnf(c_0_73, negated_conjecture, (~r1_xboole_0(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_74, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.39  cnf(c_0_75, negated_conjecture, (esk2_2(X1,k6_domain_1(u1_struct_0(esk5_0),esk7_0))=esk7_0|r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk5_0),esk7_0))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.39  cnf(c_0_76, negated_conjecture, (k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),X1))=k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_31]), c_0_57]), c_0_58]), c_0_20])]), c_0_26])).
% 0.19/0.39  cnf(c_0_77, negated_conjecture, (k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))!=k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk7_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_78, negated_conjecture, (~r1_xboole_0(k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),k6_domain_1(u1_struct_0(esk5_0),esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_56]), c_0_72])]), c_0_73])).
% 0.19/0.39  cnf(c_0_79, negated_conjecture, (r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk5_0),esk7_0))|r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.39  cnf(c_0_80, negated_conjecture, (~r2_hidden(esk7_0,k2_pre_topc(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_39]), c_0_77])).
% 0.19/0.39  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 82
% 0.19/0.39  # Proof object clause steps            : 51
% 0.19/0.39  # Proof object formula steps           : 31
% 0.19/0.39  # Proof object conjectures             : 35
% 0.19/0.39  # Proof object clause conjectures      : 32
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 23
% 0.19/0.39  # Proof object initial formulas used   : 15
% 0.19/0.39  # Proof object generating inferences   : 20
% 0.19/0.39  # Proof object simplifying inferences  : 40
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 16
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 33
% 0.19/0.39  # Removed in clause preprocessing      : 1
% 0.19/0.39  # Initial clauses in saturation        : 32
% 0.19/0.39  # Processed clauses                    : 255
% 0.19/0.39  # ...of these trivial                  : 8
% 0.19/0.39  # ...subsumed                          : 64
% 0.19/0.39  # ...remaining for further processing  : 183
% 0.19/0.39  # Other redundant clauses eliminated   : 5
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 1
% 0.19/0.39  # Backward-rewritten                   : 13
% 0.19/0.39  # Generated clauses                    : 535
% 0.19/0.39  # ...of the previous two non-trivial   : 454
% 0.19/0.39  # Contextual simplify-reflections      : 1
% 0.19/0.39  # Paramodulations                      : 531
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 5
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 135
% 0.19/0.39  #    Positive orientable unit clauses  : 29
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 10
% 0.19/0.39  #    Non-unit-clauses                  : 96
% 0.19/0.39  # Current number of unprocessed clauses: 245
% 0.19/0.39  # ...number of literals in the above   : 875
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 47
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 1980
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 1406
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 62
% 0.19/0.39  # Unit Clause-clause subsumption calls : 49
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 13
% 0.19/0.39  # BW rewrite match successes           : 4
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 12350
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.045 s
% 0.19/0.39  # System time              : 0.005 s
% 0.19/0.39  # Total time               : 0.051 s
% 0.19/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
