%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1884+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  149 (190439 expanded)
%              Number of clauses        :  116 (68101 expanded)
%              Number of leaves         :   16 (46544 expanded)
%              Depth                    :   27
%              Number of atoms          :  585 (1958259 expanded)
%              Number of equality atoms :   64 (144577 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( v4_tex_2(X2,X1)
          <=> ( v1_tdlat_3(X2)
              & ! [X3] :
                  ( ( ~ v2_struct_0(X3)
                    & v1_tdlat_3(X3)
                    & m1_pre_topc(X3,X1) )
                 => ( m1_pre_topc(X2,X3)
                   => g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tex_2)).

fof(t51_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v3_tex_2(X3,X1)
                <=> v4_tex_2(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d7_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
          <=> ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X3,X1)
                      & r1_tarski(X2,X3) )
                   => X2 = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(t34_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( ( ~ v2_struct_0(X3)
                    & v1_pre_topc(X3)
                    & v1_tdlat_3(X3)
                    & m1_pre_topc(X3,X1) )
                 => X2 != u1_struct_0(X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t5_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( u1_struct_0(X2) = u1_struct_0(X3)
               => g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tsep_1)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ( v4_tex_2(X2,X1)
            <=> ( v1_tdlat_3(X2)
                & ! [X3] :
                    ( ( ~ v2_struct_0(X3)
                      & v1_tdlat_3(X3)
                      & m1_pre_topc(X3,X1) )
                   => ( m1_pre_topc(X2,X3)
                     => g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_tex_2])).

fof(c_0_17,plain,(
    ! [X36,X37,X38] :
      ( ( ~ v3_tex_2(X38,X36)
        | v4_tex_2(X37,X36)
        | X38 != u1_struct_0(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_pre_topc(X37,X36)
        | v2_struct_0(X36)
        | ~ l1_pre_topc(X36) )
      & ( ~ v4_tex_2(X37,X36)
        | v3_tex_2(X38,X36)
        | X38 != u1_struct_0(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_pre_topc(X37,X36)
        | v2_struct_0(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t51_tex_2])])])])])).

fof(c_0_18,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_pre_topc(X24,X23)
      | m1_subset_1(u1_struct_0(X24),k1_zfmisc_1(u1_struct_0(X23))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_19,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_20,negated_conjecture,(
    ! [X45] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & ( ~ v2_struct_0(esk5_0)
        | ~ v1_tdlat_3(esk4_0)
        | ~ v4_tex_2(esk4_0,esk3_0) )
      & ( v1_tdlat_3(esk5_0)
        | ~ v1_tdlat_3(esk4_0)
        | ~ v4_tex_2(esk4_0,esk3_0) )
      & ( m1_pre_topc(esk5_0,esk3_0)
        | ~ v1_tdlat_3(esk4_0)
        | ~ v4_tex_2(esk4_0,esk3_0) )
      & ( m1_pre_topc(esk4_0,esk5_0)
        | ~ v1_tdlat_3(esk4_0)
        | ~ v4_tex_2(esk4_0,esk3_0) )
      & ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) != g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
        | ~ v1_tdlat_3(esk4_0)
        | ~ v4_tex_2(esk4_0,esk3_0) )
      & ( v1_tdlat_3(esk4_0)
        | v4_tex_2(esk4_0,esk3_0) )
      & ( v2_struct_0(X45)
        | ~ v1_tdlat_3(X45)
        | ~ m1_pre_topc(X45,esk3_0)
        | ~ m1_pre_topc(esk4_0,X45)
        | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45))
        | v4_tex_2(esk4_0,esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).

cnf(c_0_21,plain,
    ( v3_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ v4_tex_2(X1,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v2_tex_2(X27,X25)
        | v1_tdlat_3(X26)
        | X27 != u1_struct_0(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ v1_tdlat_3(X26)
        | v2_tex_2(X27,X25)
        | X27 != u1_struct_0(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

fof(c_0_24,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_25,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X8,X9,X10] :
      ( ( v2_tex_2(X9,X8)
        | ~ v3_tex_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v2_tex_2(X10,X8)
        | ~ r1_tarski(X9,X10)
        | X9 = X10
        | ~ v3_tex_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk1_2(X8,X9),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v2_tex_2(X9,X8)
        | v3_tex_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( v2_tex_2(esk1_2(X8,X9),X8)
        | ~ v2_tex_2(X9,X8)
        | v3_tex_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( r1_tarski(X9,esk1_2(X8,X9))
        | ~ v2_tex_2(X9,X8)
        | v3_tex_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( X9 != esk1_2(X8,X9)
        | ~ v2_tex_2(X9,X8)
        | v3_tex_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | v3_tex_2(u1_struct_0(X2),X1)
    | ~ v4_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( v1_tdlat_3(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | X1 != u1_struct_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X18] :
      ( v2_struct_0(X18)
      | ~ l1_struct_0(X18)
      | ~ v1_xboole_0(u1_struct_0(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_33,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_35,plain,
    ( v2_tex_2(X1,X2)
    | ~ v3_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_26]),c_0_27])])).

cnf(c_0_37,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk4_0),esk3_0)
    | ~ v4_tex_2(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_26]),c_0_27])]),c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( v1_tdlat_3(esk4_0)
    | v4_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,plain,
    ( v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_tex_2(u1_struct_0(X1),X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_41,plain,(
    ! [X28,X29] :
      ( ( ~ v2_struct_0(esk2_2(X28,X29))
        | ~ v2_tex_2(X29,X28)
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v1_pre_topc(esk2_2(X28,X29))
        | ~ v2_tex_2(X29,X28)
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v1_tdlat_3(esk2_2(X28,X29))
        | ~ v2_tex_2(X29,X28)
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( m1_pre_topc(esk2_2(X28,X29),X28)
        | ~ v2_tex_2(X29,X28)
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( X29 = u1_struct_0(esk2_2(X28,X29))
        | ~ v2_tex_2(X29,X28)
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( v2_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( v2_tex_2(u1_struct_0(esk4_0),esk3_0)
    | ~ v3_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_27])])).

cnf(c_0_46,negated_conjecture,
    ( v1_tdlat_3(esk4_0)
    | v3_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( v1_tdlat_3(esk4_0)
    | ~ v2_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_27])]),c_0_30]),c_0_40])).

cnf(c_0_48,plain,
    ( m1_pre_topc(esk2_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_40])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_tex_2(u1_struct_0(X2),X1)
    | ~ v1_tdlat_3(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_44]),c_0_22])).

cnf(c_0_52,negated_conjecture,
    ( v1_tdlat_3(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,esk1_2(X2,X1))
    | v3_tex_2(X1,X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_54,negated_conjecture,
    ( m1_pre_topc(esk2_2(esk3_0,u1_struct_0(esk4_0)),esk3_0)
    | ~ v2_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_36]),c_0_49]),c_0_27])]),c_0_30]),c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( v2_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_26]),c_0_52]),c_0_27])]),c_0_40]),c_0_30])).

cnf(c_0_56,plain,
    ( X1 = u1_struct_0(esk2_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_57,plain,
    ( v1_pre_topc(esk2_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_58,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X31,k1_zfmisc_1(X32))
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(X31,X32)
        | m1_subset_1(X31,k1_zfmisc_1(X32)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),esk1_2(esk3_0,u1_struct_0(esk4_0)))
    | v3_tex_2(u1_struct_0(esk4_0),esk3_0)
    | ~ v2_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_36]),c_0_27])])).

fof(c_0_60,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_61,negated_conjecture,
    ( m1_pre_topc(esk2_2(esk3_0,u1_struct_0(esk4_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(esk2_2(esk3_0,u1_struct_0(esk4_0))) = u1_struct_0(esk4_0)
    | ~ v2_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_36]),c_0_49]),c_0_27])]),c_0_30]),c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( v1_pre_topc(esk2_2(esk3_0,u1_struct_0(esk4_0)))
    | ~ v2_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_36]),c_0_49]),c_0_27])]),c_0_30]),c_0_50])).

cnf(c_0_64,plain,
    ( v2_tex_2(esk1_2(X1,X2),X1)
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_65,plain,(
    ! [X6,X7] :
      ( ~ v1_xboole_0(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),esk1_2(esk3_0,u1_struct_0(esk4_0)))
    | v3_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_55])])).

fof(c_0_68,plain,(
    ! [X39,X40,X41] :
      ( ~ l1_pre_topc(X39)
      | ~ m1_pre_topc(X40,X39)
      | ~ m1_pre_topc(X41,X39)
      | u1_struct_0(X40) != u1_struct_0(X41)
      | g1_pre_topc(u1_struct_0(X40),u1_pre_topc(X40)) = g1_pre_topc(u1_struct_0(X41),u1_pre_topc(X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_tsep_1])])])).

cnf(c_0_69,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( l1_pre_topc(esk2_2(esk3_0,u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_61]),c_0_27])])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(esk2_2(esk3_0,u1_struct_0(esk4_0))) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_55])])).

cnf(c_0_72,negated_conjecture,
    ( v1_pre_topc(esk2_2(esk3_0,u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_55])])).

cnf(c_0_73,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_74,negated_conjecture,
    ( v2_tex_2(esk1_2(esk3_0,u1_struct_0(esk4_0)),esk3_0)
    | v3_tex_2(u1_struct_0(esk4_0),esk3_0)
    | ~ v2_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_36]),c_0_27])])).

cnf(c_0_75,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk4_0),esk3_0)
    | m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(esk1_2(esk3_0,u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_77,plain,
    ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | u1_struct_0(X2) != u1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk2_2(esk3_0,u1_struct_0(esk4_0)))) = esk2_2(esk3_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_72])])).

fof(c_0_79,plain,(
    ! [X33,X34,X35] :
      ( ( ~ r1_tarski(u1_struct_0(X34),u1_struct_0(X35))
        | m1_pre_topc(X34,X35)
        | ~ m1_pre_topc(X35,X33)
        | ~ m1_pre_topc(X34,X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ m1_pre_topc(X34,X35)
        | r1_tarski(u1_struct_0(X34),u1_struct_0(X35))
        | ~ m1_pre_topc(X35,X33)
        | ~ m1_pre_topc(X34,X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_80,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk4_0),esk3_0)
    | m1_subset_1(esk1_2(esk3_0,u1_struct_0(esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_36]),c_0_27])]),c_0_55])])).

cnf(c_0_81,negated_conjecture,
    ( v2_tex_2(esk1_2(esk3_0,u1_struct_0(esk4_0)),esk3_0)
    | v3_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_55])])).

cnf(c_0_82,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk4_0),esk3_0)
    | ~ v1_xboole_0(esk1_2(esk3_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_50])).

cnf(c_0_83,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = esk2_2(esk3_0,u1_struct_0(esk4_0))
    | u1_struct_0(esk4_0) != u1_struct_0(X1)
    | ~ m1_pre_topc(esk2_2(esk3_0,u1_struct_0(esk4_0)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_71]),c_0_78])).

cnf(c_0_84,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( m1_pre_topc(esk2_2(esk3_0,esk1_2(esk3_0,u1_struct_0(esk4_0))),esk3_0)
    | v3_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_80]),c_0_49]),c_0_27])]),c_0_30]),c_0_81]),c_0_82])).

fof(c_0_86,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | m1_subset_1(u1_pre_topc(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_87,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = esk2_2(esk3_0,u1_struct_0(esk4_0))
    | ~ m1_pre_topc(esk2_2(esk3_0,u1_struct_0(esk4_0)),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( m1_pre_topc(X1,esk2_2(esk3_0,esk1_2(esk3_0,u1_struct_0(esk4_0))))
    | v3_tex_2(u1_struct_0(esk4_0),esk3_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(esk2_2(esk3_0,esk1_2(esk3_0,u1_struct_0(esk4_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_49]),c_0_27])])).

cnf(c_0_89,plain,
    ( v4_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ v3_tex_2(X1,X2)
    | X1 != u1_struct_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_90,plain,(
    ! [X19,X20,X21,X22] :
      ( ( X19 = X21
        | g1_pre_topc(X19,X20) != g1_pre_topc(X21,X22)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) )
      & ( X20 = X22
        | g1_pre_topc(X19,X20) != g1_pre_topc(X21,X22)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

cnf(c_0_91,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | v4_tex_2(esk4_0,esk3_0)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(esk4_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_93,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = esk2_2(esk3_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_26]),c_0_61]),c_0_27])])).

cnf(c_0_94,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_2(esk3_0,esk1_2(esk3_0,u1_struct_0(esk4_0))))
    | v3_tex_2(u1_struct_0(esk4_0),esk3_0)
    | ~ r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk2_2(esk3_0,esk1_2(esk3_0,u1_struct_0(esk4_0))))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_26])).

cnf(c_0_95,negated_conjecture,
    ( u1_struct_0(esk2_2(esk3_0,esk1_2(esk3_0,u1_struct_0(esk4_0)))) = esk1_2(esk3_0,u1_struct_0(esk4_0))
    | v3_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_80]),c_0_49]),c_0_27])]),c_0_30]),c_0_81]),c_0_82])).

cnf(c_0_96,plain,
    ( v1_tdlat_3(esk2_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_97,plain,
    ( v4_tex_2(X1,X2)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v3_tex_2(u1_struct_0(X1),X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_89]),c_0_22])).

cnf(c_0_98,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk2_2(esk3_0,u1_struct_0(esk4_0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_70]),c_0_71])).

cnf(c_0_100,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = esk2_2(esk3_0,u1_struct_0(esk4_0))
    | v4_tex_2(esk4_0,esk3_0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(esk4_0,X1) ),
    inference(rw,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_101,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_2(esk3_0,esk1_2(esk3_0,u1_struct_0(esk4_0))))
    | v3_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_67])).

cnf(c_0_102,negated_conjecture,
    ( v1_tdlat_3(esk2_2(esk3_0,esk1_2(esk3_0,u1_struct_0(esk4_0))))
    | v3_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_80]),c_0_49]),c_0_27])]),c_0_30]),c_0_81]),c_0_82])).

cnf(c_0_103,negated_conjecture,
    ( v4_tex_2(esk4_0,esk3_0)
    | ~ v3_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_26]),c_0_27])]),c_0_30])).

cnf(c_0_104,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk2_2(X1,X2))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_105,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | esk2_2(esk3_0,u1_struct_0(esk4_0)) != g1_pre_topc(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_78]),c_0_99])])).

cnf(c_0_106,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_2(esk3_0,esk1_2(esk3_0,u1_struct_0(esk4_0)))),u1_pre_topc(esk2_2(esk3_0,esk1_2(esk3_0,u1_struct_0(esk4_0))))) = esk2_2(esk3_0,u1_struct_0(esk4_0))
    | v4_tex_2(esk4_0,esk3_0)
    | v2_struct_0(esk2_2(esk3_0,esk1_2(esk3_0,u1_struct_0(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_85]),c_0_101]),c_0_102]),c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk4_0),esk3_0)
    | ~ v2_struct_0(esk2_2(esk3_0,esk1_2(esk3_0,u1_struct_0(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_80]),c_0_49]),c_0_27])]),c_0_30]),c_0_81]),c_0_82])).

cnf(c_0_108,negated_conjecture,
    ( u1_struct_0(esk2_2(esk3_0,esk1_2(esk3_0,u1_struct_0(esk4_0)))) = u1_struct_0(esk4_0)
    | v4_tex_2(esk4_0,esk3_0)
    | v2_struct_0(esk2_2(esk3_0,esk1_2(esk3_0,u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_109,negated_conjecture,
    ( u1_struct_0(esk2_2(esk3_0,esk1_2(esk3_0,u1_struct_0(esk4_0)))) = u1_struct_0(esk4_0)
    | v4_tex_2(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_103])).

cnf(c_0_110,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0)
    | ~ v1_tdlat_3(esk4_0)
    | ~ v4_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_111,plain,
    ( v3_tex_2(X1,X2)
    | X1 != esk1_2(X2,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_112,negated_conjecture,
    ( esk1_2(esk3_0,u1_struct_0(esk4_0)) = u1_struct_0(esk4_0)
    | v4_tex_2(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_109]),c_0_103])).

cnf(c_0_113,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0)
    | ~ v1_tdlat_3(esk4_0)
    | ~ v4_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_114,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0)
    | ~ v4_tex_2(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_52])])).

cnf(c_0_115,negated_conjecture,
    ( v4_tex_2(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_55]),c_0_36]),c_0_27])]),c_0_103])).

cnf(c_0_116,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0)
    | ~ v4_tex_2(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_52])])).

cnf(c_0_117,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_115])])).

cnf(c_0_118,negated_conjecture,
    ( v1_tdlat_3(esk5_0)
    | ~ v1_tdlat_3(esk4_0)
    | ~ v4_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_119,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    | ~ v1_tdlat_3(esk4_0)
    | ~ v4_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_120,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) != g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | ~ v1_tdlat_3(esk4_0)
    | ~ v4_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_121,plain,
    ( X3 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tex_2(X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ v3_tex_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_122,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_115])])).

cnf(c_0_123,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_117]),c_0_27])])).

cnf(c_0_124,negated_conjecture,
    ( v1_tdlat_3(esk5_0)
    | ~ v4_tex_2(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_52])])).

cnf(c_0_125,negated_conjecture,
    ( ~ v4_tex_2(esk4_0,esk3_0)
    | ~ v2_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_52])])).

cnf(c_0_126,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))
    | ~ v4_tex_2(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_52])])).

cnf(c_0_127,negated_conjecture,
    ( X1 = u1_struct_0(esk4_0)
    | ~ r1_tarski(u1_struct_0(esk4_0),X1)
    | ~ v2_tex_2(X1,esk3_0)
    | ~ v3_tex_2(u1_struct_0(esk4_0),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_36]),c_0_27])])).

cnf(c_0_128,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_115])])).

cnf(c_0_129,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_130,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_122]),c_0_123])])).

cnf(c_0_131,negated_conjecture,
    ( v1_tdlat_3(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_115])])).

cnf(c_0_132,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_115])])).

cnf(c_0_133,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != esk2_2(esk3_0,u1_struct_0(esk4_0))
    | ~ v4_tex_2(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_126,c_0_93])).

cnf(c_0_134,negated_conjecture,
    ( X1 = u1_struct_0(esk4_0)
    | ~ r1_tarski(u1_struct_0(esk4_0),X1)
    | ~ v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_128])])).

cnf(c_0_135,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_117]),c_0_27])])).

cnf(c_0_136,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_137,negated_conjecture,
    ( v2_tex_2(u1_struct_0(esk5_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_117]),c_0_131]),c_0_27])]),c_0_132]),c_0_30])).

cnf(c_0_138,negated_conjecture,
    ( m1_pre_topc(X1,esk5_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_117]),c_0_49]),c_0_27])])).

cnf(c_0_139,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != esk2_2(esk3_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_115])])).

cnf(c_0_140,negated_conjecture,
    ( u1_struct_0(esk5_0) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_136]),c_0_137])])).

cnf(c_0_141,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0)
    | ~ r1_tarski(u1_struct_0(esk5_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_138,c_0_117])).

cnf(c_0_142,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk5_0)) != esk2_2(esk3_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_143,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0)
    | ~ r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_141,c_0_140]),c_0_140])).

cnf(c_0_144,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_136,c_0_140])).

cnf(c_0_145,negated_conjecture,
    ( ~ m1_pre_topc(esk2_2(esk3_0,u1_struct_0(esk4_0)),X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_140]),c_0_142])).

cnf(c_0_146,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_143,c_0_144])])).

cnf(c_0_147,negated_conjecture,
    ( m1_pre_topc(esk2_2(esk3_0,u1_struct_0(esk4_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_61]),c_0_71]),c_0_136])])).

cnf(c_0_148,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_146]),c_0_147]),c_0_123])]),
    [proof]).

%------------------------------------------------------------------------------
