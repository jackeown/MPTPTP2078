%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:33 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :  109 (1661 expanded)
%              Number of clauses        :   74 ( 613 expanded)
%              Number of leaves         :   17 ( 415 expanded)
%              Depth                    :   14
%              Number of atoms          :  337 (7411 expanded)
%              Number of equality atoms :   44 ( 754 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v7_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(k1_tex_2(X1,X3)),u1_pre_topc(k1_tex_2(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tex_2)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(rc7_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2)
          & v1_pre_topc(X2)
          & ~ v1_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_tex_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(d4_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_tex_2(X1,X2)
              <=> u1_struct_0(X3) = k6_domain_1(u1_struct_0(X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(fc7_struct_0,axiom,(
    ! [X1] :
      ( ( v7_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(cc10_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v7_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ~ v2_struct_0(X2)
           => ( ~ v2_struct_0(X2)
              & ~ v1_tex_2(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

fof(t16_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_tex_2(X2,X1)
            & m1_pre_topc(X2,X1) )
         => g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tex_2)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v7_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(k1_tex_2(X1,X3)),u1_pre_topc(k1_tex_2(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_tex_2])).

fof(c_0_18,plain,(
    ! [X28,X29] :
      ( ( ~ v2_struct_0(k1_tex_2(X28,X29))
        | v2_struct_0(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28)) )
      & ( v1_pre_topc(k1_tex_2(X28,X29))
        | v2_struct_0(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28)) )
      & ( m1_pre_topc(k1_tex_2(X28,X29),X28)
        | v2_struct_0(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_19,plain,(
    ! [X4] : m1_subset_1(esk1_1(X4),X4) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_20,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | l1_pre_topc(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_21,negated_conjecture,(
    ! [X42] :
      ( ~ v2_struct_0(esk4_0)
      & l1_pre_topc(esk4_0)
      & ~ v2_struct_0(esk5_0)
      & v7_struct_0(esk5_0)
      & m1_pre_topc(esk5_0,esk4_0)
      & ( ~ m1_subset_1(X42,u1_struct_0(esk4_0))
        | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(u1_struct_0(k1_tex_2(esk4_0,X42)),u1_pre_topc(k1_tex_2(esk4_0,X42))) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])])).

cnf(c_0_22,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X32] :
      ( ( m1_pre_topc(esk3_1(X32),X32)
        | v2_struct_0(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ v2_struct_0(esk3_1(X32))
        | v2_struct_0(X32)
        | ~ l1_pre_topc(X32) )
      & ( v1_pre_topc(esk3_1(X32))
        | v2_struct_0(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ v1_tex_2(esk3_1(X32),X32)
        | v2_struct_0(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_tex_2])])])])])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tex_2(X1,esk1_1(u1_struct_0(X1))),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( m1_pre_topc(esk3_1(X1),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk5_0,esk1_1(u1_struct_0(esk5_0))),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_35,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ m1_pre_topc(X15,X14)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | m1_subset_1(X16,u1_struct_0(X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk3_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_30])).

fof(c_0_37,plain,(
    ! [X25,X26,X27] :
      ( ( X27 != k1_tex_2(X25,X26)
        | u1_struct_0(X27) = k6_domain_1(u1_struct_0(X25),X26)
        | v2_struct_0(X27)
        | ~ v1_pre_topc(X27)
        | ~ m1_pre_topc(X27,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25) )
      & ( u1_struct_0(X27) != k6_domain_1(u1_struct_0(X25),X26)
        | X27 = k1_tex_2(X25,X26)
        | v2_struct_0(X27)
        | ~ v1_pre_topc(X27)
        | ~ m1_pre_topc(X27,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).

fof(c_0_38,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | r1_tarski(u1_struct_0(X22),u1_struct_0(X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

fof(c_0_39,plain,(
    ! [X11] :
      ( ~ v7_struct_0(X11)
      | ~ l1_struct_0(X11)
      | v1_zfmisc_1(u1_struct_0(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_40,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_41,plain,(
    ! [X10] :
      ( v2_struct_0(X10)
      | ~ l1_struct_0(X10)
      | ~ v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(k1_tex_2(esk5_0,esk1_1(u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_33]),c_0_29])])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,esk1_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_23])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(esk3_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_36]),c_0_29])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(esk3_1(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_48,plain,
    ( u1_struct_0(X1) = k6_domain_1(u1_struct_0(X2),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | X1 != k1_tex_2(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( v1_pre_topc(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_50,plain,(
    ! [X36,X37] :
      ( v1_xboole_0(X36)
      | v1_xboole_0(X37)
      | ~ v1_zfmisc_1(X37)
      | ~ r1_tarski(X36,X37)
      | X36 = X37 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_51,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( v7_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( l1_struct_0(k1_tex_2(esk5_0,esk1_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_42])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_struct_0(k1_tex_2(esk5_0,esk1_1(u1_struct_0(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_29]),c_0_30])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_25]),c_0_26])]),c_0_30]),c_0_45])).

fof(c_0_59,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(X6)
      | ~ v1_pre_topc(X6)
      | X6 = g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_60,plain,
    ( v1_pre_topc(esk3_1(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_61,negated_conjecture,
    ( l1_struct_0(esk3_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_46])).

cnf(c_0_62,negated_conjecture,
    ( ~ v2_struct_0(esk3_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_29]),c_0_30])).

fof(c_0_63,plain,(
    ! [X17,X18] :
      ( v1_xboole_0(X17)
      | ~ m1_subset_1(X18,X17)
      | k6_domain_1(X17,X18) = k1_tarski(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_64,plain,
    ( k6_domain_1(u1_struct_0(X1),X2) = u1_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_49]),c_0_22]),c_0_34])).

cnf(c_0_65,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(u1_struct_0(k1_tex_2(esk5_0,esk1_1(u1_struct_0(esk5_0)))),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_33]),c_0_29])])).

cnf(c_0_67,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_53]),c_0_30])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(k1_tex_2(esk5_0,esk1_1(u1_struct_0(esk5_0))))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_26])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk1_1(u1_struct_0(esk5_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_23])).

cnf(c_0_72,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( v1_pre_topc(esk3_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_29]),c_0_30])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_1(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_36]),c_0_29])])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_1(esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_61]),c_0_62])).

fof(c_0_76,plain,(
    ! [X23,X24] :
      ( ( ~ v2_struct_0(X24)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ v7_struct_0(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ v1_tex_2(X24,X23)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ v7_struct_0(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).

cnf(c_0_77,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_78,plain,
    ( k6_domain_1(u1_struct_0(X1),esk1_1(u1_struct_0(X1))) = u1_struct_0(k1_tex_2(X1,esk1_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_23])).

cnf(c_0_79,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk5_0,esk1_1(u1_struct_0(esk5_0)))) = u1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])]),c_0_68]),c_0_69])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_70]),c_0_45])).

cnf(c_0_81,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk1_1(u1_struct_0(esk5_0))) = u1_struct_0(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_71]),c_0_26])]),c_0_45])).

fof(c_0_82,plain,(
    ! [X34,X35] :
      ( v2_struct_0(X34)
      | ~ l1_pre_topc(X34)
      | v1_tex_2(X35,X34)
      | ~ m1_pre_topc(X35,X34)
      | g1_pre_topc(u1_struct_0(X35),u1_pre_topc(X35)) = g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t16_tex_2])])])])).

cnf(c_0_83,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_1(esk5_0)),u1_pre_topc(esk3_1(esk5_0))) = esk3_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_46]),c_0_73])])).

cnf(c_0_84,negated_conjecture,
    ( u1_struct_0(esk3_1(esk5_0)) = u1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_74]),c_0_67])]),c_0_68]),c_0_75])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v7_struct_0(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_86,plain,
    ( k6_domain_1(X1,esk1_1(X1)) = k1_tarski(esk1_1(X1))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_23])).

cnf(c_0_87,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk5_0),esk1_1(u1_struct_0(esk5_0))) = u1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_29]),c_0_79]),c_0_30])).

cnf(c_0_88,negated_conjecture,
    ( k1_tarski(esk1_1(u1_struct_0(esk5_0))) = u1_struct_0(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0)))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_71]),c_0_80]),c_0_81])).

fof(c_0_89,plain,(
    ! [X19,X20] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))
        | ~ m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)),X19)
        | ~ m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

cnf(c_0_90,plain,
    ( v2_struct_0(X1)
    | v1_tex_2(X2,X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk3_1(esk5_0))) = esk3_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( ~ v1_tex_2(esk3_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_36]),c_0_54]),c_0_29])]),c_0_30]),c_0_62])).

cnf(c_0_93,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0))),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_71]),c_0_26])]),c_0_45])).

cnf(c_0_94,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0)))) = u1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_68])).

cnf(c_0_95,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(u1_struct_0(k1_tex_2(esk4_0,X1)),u1_pre_topc(k1_tex_2(esk4_0,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_97,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) = esk3_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_36]),c_0_84]),c_0_91]),c_0_29])]),c_0_92]),c_0_30])).

cnf(c_0_98,negated_conjecture,
    ( l1_pre_topc(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_93]),c_0_26])])).

cnf(c_0_99,negated_conjecture,
    ( v1_pre_topc(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_71]),c_0_26])]),c_0_45])).

cnf(c_0_100,plain,
    ( X1 = k1_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(X1) != k6_domain_1(u1_struct_0(X2),X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_101,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk1_1(u1_struct_0(esk5_0))) = u1_struct_0(esk5_0) ),
    inference(rw,[status(thm)],[c_0_81,c_0_94])).

cnf(c_0_102,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_25]),c_0_26])])).

cnf(c_0_103,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(esk4_0,X1)),u1_pre_topc(k1_tex_2(esk4_0,X1))) != esk3_1(esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0)))),u1_pre_topc(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0))))) = k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_98]),c_0_99])])).

cnf(c_0_105,negated_conjecture,
    ( X1 = k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0)))
    | v2_struct_0(X1)
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ v1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_26]),c_0_71])]),c_0_45])).

cnf(c_0_106,negated_conjecture,
    ( m1_pre_topc(esk3_1(esk5_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_102,c_0_97])).

cnf(c_0_107,negated_conjecture,
    ( k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0))) != esk3_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_71])])).

cnf(c_0_108,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_84]),c_0_106]),c_0_73])]),c_0_107]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n011.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 10:38:12 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.16/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.16/0.39  # and selection function SelectGrCQArEqFirst.
% 0.16/0.39  #
% 0.16/0.39  # Preprocessing time       : 0.016 s
% 0.16/0.39  # Presaturation interreduction done
% 0.16/0.39  
% 0.16/0.39  # Proof found!
% 0.16/0.39  # SZS status Theorem
% 0.16/0.39  # SZS output start CNFRefutation
% 0.16/0.39  fof(t23_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v7_struct_0(X2))&m1_pre_topc(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(k1_tex_2(X1,X3)),u1_pre_topc(k1_tex_2(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tex_2)).
% 0.16/0.39  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.16/0.39  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.16/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.16/0.39  fof(rc7_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>?[X2]:(((m1_pre_topc(X2,X1)&~(v2_struct_0(X2)))&v1_pre_topc(X2))&~(v1_tex_2(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_tex_2)).
% 0.16/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.16/0.39  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.16/0.39  fof(d4_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))=>(X3=k1_tex_2(X1,X2)<=>u1_struct_0(X3)=k6_domain_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 0.16/0.39  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.16/0.39  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.16/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.16/0.39  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.16/0.39  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.16/0.39  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.16/0.39  fof(cc10_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v7_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(~(v2_struct_0(X2))=>(~(v2_struct_0(X2))&~(v1_tex_2(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 0.16/0.39  fof(t16_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_tex_2(X2,X1))&m1_pre_topc(X2,X1))=>g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tex_2)).
% 0.16/0.39  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 0.16/0.39  fof(c_0_17, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v7_struct_0(X2))&m1_pre_topc(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(k1_tex_2(X1,X3)),u1_pre_topc(k1_tex_2(X1,X3))))))), inference(assume_negation,[status(cth)],[t23_tex_2])).
% 0.16/0.39  fof(c_0_18, plain, ![X28, X29]:(((~v2_struct_0(k1_tex_2(X28,X29))|(v2_struct_0(X28)|~l1_pre_topc(X28)|~m1_subset_1(X29,u1_struct_0(X28))))&(v1_pre_topc(k1_tex_2(X28,X29))|(v2_struct_0(X28)|~l1_pre_topc(X28)|~m1_subset_1(X29,u1_struct_0(X28)))))&(m1_pre_topc(k1_tex_2(X28,X29),X28)|(v2_struct_0(X28)|~l1_pre_topc(X28)|~m1_subset_1(X29,u1_struct_0(X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.16/0.39  fof(c_0_19, plain, ![X4]:m1_subset_1(esk1_1(X4),X4), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.16/0.39  fof(c_0_20, plain, ![X8, X9]:(~l1_pre_topc(X8)|(~m1_pre_topc(X9,X8)|l1_pre_topc(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.16/0.39  fof(c_0_21, negated_conjecture, ![X42]:((~v2_struct_0(esk4_0)&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v7_struct_0(esk5_0))&m1_pre_topc(esk5_0,esk4_0))&(~m1_subset_1(X42,u1_struct_0(esk4_0))|g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))!=g1_pre_topc(u1_struct_0(k1_tex_2(esk4_0,X42)),u1_pre_topc(k1_tex_2(esk4_0,X42)))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])])).
% 0.16/0.39  cnf(c_0_22, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.16/0.39  cnf(c_0_23, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.16/0.39  cnf(c_0_24, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.16/0.39  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.16/0.39  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.16/0.39  fof(c_0_27, plain, ![X32]:((((m1_pre_topc(esk3_1(X32),X32)|(v2_struct_0(X32)|~l1_pre_topc(X32)))&(~v2_struct_0(esk3_1(X32))|(v2_struct_0(X32)|~l1_pre_topc(X32))))&(v1_pre_topc(esk3_1(X32))|(v2_struct_0(X32)|~l1_pre_topc(X32))))&(~v1_tex_2(esk3_1(X32),X32)|(v2_struct_0(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_tex_2])])])])])).
% 0.16/0.39  cnf(c_0_28, plain, (v2_struct_0(X1)|m1_pre_topc(k1_tex_2(X1,esk1_1(u1_struct_0(X1))),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.16/0.39  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.16/0.39  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.16/0.39  cnf(c_0_31, plain, (m1_pre_topc(esk3_1(X1),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.16/0.39  fof(c_0_32, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.16/0.39  cnf(c_0_33, negated_conjecture, (m1_pre_topc(k1_tex_2(esk5_0,esk1_1(u1_struct_0(esk5_0))),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.16/0.39  cnf(c_0_34, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.16/0.39  fof(c_0_35, plain, ![X14, X15, X16]:(v2_struct_0(X14)|~l1_pre_topc(X14)|(v2_struct_0(X15)|~m1_pre_topc(X15,X14)|(~m1_subset_1(X16,u1_struct_0(X15))|m1_subset_1(X16,u1_struct_0(X14))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.16/0.39  cnf(c_0_36, negated_conjecture, (m1_pre_topc(esk3_1(esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_29]), c_0_30])).
% 0.16/0.39  fof(c_0_37, plain, ![X25, X26, X27]:((X27!=k1_tex_2(X25,X26)|u1_struct_0(X27)=k6_domain_1(u1_struct_0(X25),X26)|(v2_struct_0(X27)|~v1_pre_topc(X27)|~m1_pre_topc(X27,X25))|~m1_subset_1(X26,u1_struct_0(X25))|(v2_struct_0(X25)|~l1_pre_topc(X25)))&(u1_struct_0(X27)!=k6_domain_1(u1_struct_0(X25),X26)|X27=k1_tex_2(X25,X26)|(v2_struct_0(X27)|~v1_pre_topc(X27)|~m1_pre_topc(X27,X25))|~m1_subset_1(X26,u1_struct_0(X25))|(v2_struct_0(X25)|~l1_pre_topc(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).
% 0.16/0.39  fof(c_0_38, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_pre_topc(X22,X21)|r1_tarski(u1_struct_0(X22),u1_struct_0(X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.16/0.39  fof(c_0_39, plain, ![X11]:(~v7_struct_0(X11)|~l1_struct_0(X11)|v1_zfmisc_1(u1_struct_0(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.16/0.39  cnf(c_0_40, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.16/0.39  fof(c_0_41, plain, ![X10]:(v2_struct_0(X10)|~l1_struct_0(X10)|~v1_xboole_0(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.16/0.39  cnf(c_0_42, negated_conjecture, (l1_pre_topc(k1_tex_2(esk5_0,esk1_1(u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_33]), c_0_29])])).
% 0.16/0.39  cnf(c_0_43, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,esk1_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_34, c_0_23])).
% 0.16/0.39  cnf(c_0_44, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.16/0.39  cnf(c_0_45, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.16/0.39  cnf(c_0_46, negated_conjecture, (l1_pre_topc(esk3_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_36]), c_0_29])])).
% 0.16/0.39  cnf(c_0_47, plain, (v2_struct_0(X1)|~v2_struct_0(esk3_1(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.16/0.39  cnf(c_0_48, plain, (u1_struct_0(X1)=k6_domain_1(u1_struct_0(X2),X3)|v2_struct_0(X1)|v2_struct_0(X2)|X1!=k1_tex_2(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.16/0.39  cnf(c_0_49, plain, (v1_pre_topc(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.16/0.39  fof(c_0_50, plain, ![X36, X37]:(v1_xboole_0(X36)|(v1_xboole_0(X37)|~v1_zfmisc_1(X37)|(~r1_tarski(X36,X37)|X36=X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.16/0.39  cnf(c_0_51, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.16/0.39  cnf(c_0_52, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.16/0.39  cnf(c_0_53, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_40, c_0_29])).
% 0.16/0.39  cnf(c_0_54, negated_conjecture, (v7_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.16/0.39  cnf(c_0_55, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.16/0.39  cnf(c_0_56, negated_conjecture, (l1_struct_0(k1_tex_2(esk5_0,esk1_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_40, c_0_42])).
% 0.16/0.39  cnf(c_0_57, negated_conjecture, (~v2_struct_0(k1_tex_2(esk5_0,esk1_1(u1_struct_0(esk5_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_29]), c_0_30])).
% 0.16/0.39  cnf(c_0_58, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_25]), c_0_26])]), c_0_30]), c_0_45])).
% 0.16/0.39  fof(c_0_59, plain, ![X6]:(~l1_pre_topc(X6)|(~v1_pre_topc(X6)|X6=g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.16/0.39  cnf(c_0_60, plain, (v1_pre_topc(esk3_1(X1))|v2_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.16/0.39  cnf(c_0_61, negated_conjecture, (l1_struct_0(esk3_1(esk5_0))), inference(spm,[status(thm)],[c_0_40, c_0_46])).
% 0.16/0.39  cnf(c_0_62, negated_conjecture, (~v2_struct_0(esk3_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_29]), c_0_30])).
% 0.16/0.39  fof(c_0_63, plain, ![X17, X18]:(v1_xboole_0(X17)|~m1_subset_1(X18,X17)|k6_domain_1(X17,X18)=k1_tarski(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.16/0.39  cnf(c_0_64, plain, (k6_domain_1(u1_struct_0(X1),X2)=u1_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]), c_0_49]), c_0_22]), c_0_34])).
% 0.16/0.39  cnf(c_0_65, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.16/0.39  cnf(c_0_66, negated_conjecture, (r1_tarski(u1_struct_0(k1_tex_2(esk5_0,esk1_1(u1_struct_0(esk5_0)))),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_33]), c_0_29])])).
% 0.16/0.39  cnf(c_0_67, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 0.16/0.39  cnf(c_0_68, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_53]), c_0_30])).
% 0.16/0.39  cnf(c_0_69, negated_conjecture, (~v1_xboole_0(u1_struct_0(k1_tex_2(esk5_0,esk1_1(u1_struct_0(esk5_0)))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.16/0.39  cnf(c_0_70, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_26])).
% 0.16/0.39  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk1_1(u1_struct_0(esk5_0)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_58, c_0_23])).
% 0.16/0.39  cnf(c_0_72, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.16/0.39  cnf(c_0_73, negated_conjecture, (v1_pre_topc(esk3_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_29]), c_0_30])).
% 0.16/0.39  cnf(c_0_74, negated_conjecture, (r1_tarski(u1_struct_0(esk3_1(esk5_0)),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_36]), c_0_29])])).
% 0.16/0.39  cnf(c_0_75, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_1(esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_61]), c_0_62])).
% 0.16/0.39  fof(c_0_76, plain, ![X23, X24]:((~v2_struct_0(X24)|v2_struct_0(X24)|~m1_pre_topc(X24,X23)|(v2_struct_0(X23)|~v7_struct_0(X23)|~l1_pre_topc(X23)))&(~v1_tex_2(X24,X23)|v2_struct_0(X24)|~m1_pre_topc(X24,X23)|(v2_struct_0(X23)|~v7_struct_0(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).
% 0.16/0.39  cnf(c_0_77, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.16/0.39  cnf(c_0_78, plain, (k6_domain_1(u1_struct_0(X1),esk1_1(u1_struct_0(X1)))=u1_struct_0(k1_tex_2(X1,esk1_1(u1_struct_0(X1))))|v2_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_64, c_0_23])).
% 0.16/0.39  cnf(c_0_79, negated_conjecture, (u1_struct_0(k1_tex_2(esk5_0,esk1_1(u1_struct_0(esk5_0))))=u1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])]), c_0_68]), c_0_69])).
% 0.16/0.39  cnf(c_0_80, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_70]), c_0_45])).
% 0.16/0.39  cnf(c_0_81, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk1_1(u1_struct_0(esk5_0)))=u1_struct_0(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_71]), c_0_26])]), c_0_45])).
% 0.16/0.39  fof(c_0_82, plain, ![X34, X35]:(v2_struct_0(X34)|~l1_pre_topc(X34)|(v1_tex_2(X35,X34)|~m1_pre_topc(X35,X34)|g1_pre_topc(u1_struct_0(X35),u1_pre_topc(X35))=g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t16_tex_2])])])])).
% 0.16/0.39  cnf(c_0_83, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_1(esk5_0)),u1_pre_topc(esk3_1(esk5_0)))=esk3_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_46]), c_0_73])])).
% 0.16/0.39  cnf(c_0_84, negated_conjecture, (u1_struct_0(esk3_1(esk5_0))=u1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_74]), c_0_67])]), c_0_68]), c_0_75])).
% 0.16/0.39  cnf(c_0_85, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~v7_struct_0(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.16/0.39  cnf(c_0_86, plain, (k6_domain_1(X1,esk1_1(X1))=k1_tarski(esk1_1(X1))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_77, c_0_23])).
% 0.16/0.39  cnf(c_0_87, negated_conjecture, (k6_domain_1(u1_struct_0(esk5_0),esk1_1(u1_struct_0(esk5_0)))=u1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_29]), c_0_79]), c_0_30])).
% 0.16/0.39  cnf(c_0_88, negated_conjecture, (k1_tarski(esk1_1(u1_struct_0(esk5_0)))=u1_struct_0(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0))))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_71]), c_0_80]), c_0_81])).
% 0.16/0.39  fof(c_0_89, plain, ![X19, X20]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))|~m1_pre_topc(X20,X19)|~l1_pre_topc(X19))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)),X19)|~m1_pre_topc(X20,X19)|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 0.16/0.39  cnf(c_0_90, plain, (v2_struct_0(X1)|v1_tex_2(X2,X1)|g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.16/0.39  cnf(c_0_91, negated_conjecture, (g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk3_1(esk5_0)))=esk3_1(esk5_0)), inference(rw,[status(thm)],[c_0_83, c_0_84])).
% 0.16/0.39  cnf(c_0_92, negated_conjecture, (~v1_tex_2(esk3_1(esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_36]), c_0_54]), c_0_29])]), c_0_30]), c_0_62])).
% 0.16/0.39  cnf(c_0_93, negated_conjecture, (m1_pre_topc(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0))),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_71]), c_0_26])]), c_0_45])).
% 0.16/0.39  cnf(c_0_94, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0))))=u1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), c_0_68])).
% 0.16/0.39  cnf(c_0_95, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.16/0.39  cnf(c_0_96, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk4_0))|g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))!=g1_pre_topc(u1_struct_0(k1_tex_2(esk4_0,X1)),u1_pre_topc(k1_tex_2(esk4_0,X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.16/0.39  cnf(c_0_97, negated_conjecture, (g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))=esk3_1(esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_36]), c_0_84]), c_0_91]), c_0_29])]), c_0_92]), c_0_30])).
% 0.16/0.39  cnf(c_0_98, negated_conjecture, (l1_pre_topc(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_93]), c_0_26])])).
% 0.16/0.39  cnf(c_0_99, negated_conjecture, (v1_pre_topc(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_71]), c_0_26])]), c_0_45])).
% 0.16/0.39  cnf(c_0_100, plain, (X1=k1_tex_2(X2,X3)|v2_struct_0(X1)|v2_struct_0(X2)|u1_struct_0(X1)!=k6_domain_1(u1_struct_0(X2),X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.16/0.39  cnf(c_0_101, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk1_1(u1_struct_0(esk5_0)))=u1_struct_0(esk5_0)), inference(rw,[status(thm)],[c_0_81, c_0_94])).
% 0.16/0.39  cnf(c_0_102, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_25]), c_0_26])])).
% 0.16/0.39  cnf(c_0_103, negated_conjecture, (g1_pre_topc(u1_struct_0(k1_tex_2(esk4_0,X1)),u1_pre_topc(k1_tex_2(esk4_0,X1)))!=esk3_1(esk5_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_96, c_0_97])).
% 0.16/0.39  cnf(c_0_104, negated_conjecture, (g1_pre_topc(u1_struct_0(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0)))),u1_pre_topc(k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0)))))=k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_98]), c_0_99])])).
% 0.16/0.39  cnf(c_0_105, negated_conjecture, (X1=k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0)))|v2_struct_0(X1)|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~m1_pre_topc(X1,esk4_0)|~v1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_26]), c_0_71])]), c_0_45])).
% 0.16/0.39  cnf(c_0_106, negated_conjecture, (m1_pre_topc(esk3_1(esk5_0),esk4_0)), inference(rw,[status(thm)],[c_0_102, c_0_97])).
% 0.16/0.39  cnf(c_0_107, negated_conjecture, (k1_tex_2(esk4_0,esk1_1(u1_struct_0(esk5_0)))!=esk3_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_71])])).
% 0.16/0.39  cnf(c_0_108, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_84]), c_0_106]), c_0_73])]), c_0_107]), c_0_62]), ['proof']).
% 0.16/0.39  # SZS output end CNFRefutation
% 0.16/0.39  # Proof object total steps             : 109
% 0.16/0.39  # Proof object clause steps            : 74
% 0.16/0.39  # Proof object formula steps           : 35
% 0.16/0.39  # Proof object conjectures             : 51
% 0.16/0.39  # Proof object clause conjectures      : 48
% 0.16/0.39  # Proof object formula conjectures     : 3
% 0.16/0.39  # Proof object initial clauses used    : 27
% 0.16/0.39  # Proof object initial formulas used   : 17
% 0.16/0.39  # Proof object generating inferences   : 42
% 0.16/0.39  # Proof object simplifying inferences  : 86
% 0.16/0.39  # Training examples: 0 positive, 0 negative
% 0.16/0.39  # Parsed axioms                        : 20
% 0.16/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.39  # Initial clauses                      : 37
% 0.16/0.39  # Removed in clause preprocessing      : 1
% 0.16/0.39  # Initial clauses in saturation        : 36
% 0.16/0.39  # Processed clauses                    : 1231
% 0.16/0.39  # ...of these trivial                  : 28
% 0.16/0.39  # ...subsumed                          : 212
% 0.16/0.39  # ...remaining for further processing  : 991
% 0.16/0.39  # Other redundant clauses eliminated   : 1
% 0.16/0.39  # Clauses deleted for lack of memory   : 0
% 0.16/0.39  # Backward-subsumed                    : 0
% 0.16/0.39  # Backward-rewritten                   : 392
% 0.16/0.39  # Generated clauses                    : 1838
% 0.16/0.39  # ...of the previous two non-trivial   : 2020
% 0.16/0.39  # Contextual simplify-reflections      : 3
% 0.16/0.39  # Paramodulations                      : 1834
% 0.16/0.39  # Factorizations                       : 0
% 0.16/0.39  # Equation resolutions                 : 4
% 0.16/0.39  # Propositional unsat checks           : 0
% 0.16/0.39  #    Propositional check models        : 0
% 0.16/0.39  #    Propositional check unsatisfiable : 0
% 0.16/0.39  #    Propositional clauses             : 0
% 0.16/0.39  #    Propositional clauses after purity: 0
% 0.16/0.39  #    Propositional unsat core size     : 0
% 0.16/0.39  #    Propositional preprocessing time  : 0.000
% 0.16/0.39  #    Propositional encoding time       : 0.000
% 0.16/0.39  #    Propositional solver time         : 0.000
% 0.16/0.39  #    Success case prop preproc time    : 0.000
% 0.16/0.39  #    Success case prop encoding time   : 0.000
% 0.16/0.39  #    Success case prop solver time     : 0.000
% 0.16/0.39  # Current number of processed clauses  : 564
% 0.16/0.39  #    Positive orientable unit clauses  : 252
% 0.16/0.39  #    Positive unorientable unit clauses: 0
% 0.16/0.39  #    Negative unit clauses             : 163
% 0.16/0.39  #    Non-unit-clauses                  : 149
% 0.16/0.39  # Current number of unprocessed clauses: 777
% 0.16/0.39  # ...number of literals in the above   : 1169
% 0.16/0.39  # Current number of archived formulas  : 0
% 0.16/0.39  # Current number of archived clauses   : 426
% 0.16/0.39  # Clause-clause subsumption calls (NU) : 3734
% 0.16/0.39  # Rec. Clause-clause subsumption calls : 2591
% 0.16/0.39  # Non-unit clause-clause subsumptions  : 80
% 0.16/0.39  # Unit Clause-clause subsumption calls : 5501
% 0.16/0.39  # Rewrite failures with RHS unbound    : 0
% 0.16/0.39  # BW rewrite match attempts            : 965
% 0.16/0.39  # BW rewrite match successes           : 33
% 0.16/0.39  # Condensation attempts                : 0
% 0.16/0.39  # Condensation successes               : 0
% 0.16/0.39  # Termbank termtop insertions          : 51021
% 0.16/0.39  
% 0.16/0.39  # -------------------------------------------------
% 0.16/0.39  # User time                : 0.066 s
% 0.16/0.39  # System time              : 0.005 s
% 0.16/0.39  # Total time               : 0.071 s
% 0.16/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
