%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:30 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 (5380 expanded)
%              Number of clauses        :   77 (1882 expanded)
%              Number of leaves         :   19 (1307 expanded)
%              Depth                    :   14
%              Number of atoms          :  477 (30846 expanded)
%              Number of equality atoms :   53 (1093 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
          <=> ~ v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(t47_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v3_pre_topc(X2,X1)
              & v3_tex_2(X2,X1) )
           => v1_tops_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

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

fof(t11_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( ( v1_borsuk_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> v4_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).

fof(cc5_tdlat_3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_borsuk_1(X2,X1)
            & v1_tsep_1(X2,X1)
            & v1_tdlat_3(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

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

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t43_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => v2_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d2_tops_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

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

fof(rc7_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2)
          & v4_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(t48_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v1_tops_1(X2,X1)
              & v2_tex_2(X2,X1) )
           => v3_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(cc4_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ~ v1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

fof(cc2_subset_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( ~ v1_subset_1(X2,X1)
           => ~ v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_tex_2(X2,X1)
            <=> ~ v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_tex_2])).

fof(c_0_20,plain,(
    ! [X59,X60] :
      ( v2_struct_0(X59)
      | ~ v2_pre_topc(X59)
      | ~ l1_pre_topc(X59)
      | ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))
      | ~ v3_pre_topc(X60,X59)
      | ~ v3_tex_2(X60,X59)
      | v1_tops_1(X60,X59) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).

fof(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & v1_tdlat_3(esk5_0)
    & l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ( ~ v3_tex_2(esk6_0,esk5_0)
      | v1_subset_1(esk6_0,u1_struct_0(esk5_0)) )
    & ( v3_tex_2(esk6_0,esk5_0)
      | ~ v1_subset_1(esk6_0,u1_struct_0(esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_22,plain,(
    ! [X52,X53] :
      ( ( ~ v1_tdlat_3(X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
        | v3_pre_topc(X53,X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) )
      & ( m1_subset_1(esk4_1(X52),k1_zfmisc_1(u1_struct_0(X52)))
        | v1_tdlat_3(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) )
      & ( ~ v3_pre_topc(esk4_1(X52),X52)
        | v1_tdlat_3(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).

fof(c_0_23,plain,(
    ! [X39] :
      ( ~ l1_pre_topc(X39)
      | ~ v1_tdlat_3(X39)
      | v2_pre_topc(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

fof(c_0_24,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v1_borsuk_1(X35,X34)
        | ~ m1_pre_topc(X35,X34)
        | v4_pre_topc(X36,X34)
        | X36 != u1_struct_0(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ m1_pre_topc(X35,X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( v1_borsuk_1(X35,X34)
        | ~ v4_pre_topc(X36,X34)
        | X36 != u1_struct_0(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ m1_pre_topc(X35,X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_pre_topc(X35,X34)
        | ~ v4_pre_topc(X36,X34)
        | X36 != u1_struct_0(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ m1_pre_topc(X35,X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tsep_1])])])])).

fof(c_0_25,plain,(
    ! [X40,X41] :
      ( ( v1_borsuk_1(X41,X40)
        | ~ m1_pre_topc(X41,X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ v1_tdlat_3(X40)
        | ~ l1_pre_topc(X40) )
      & ( v1_tsep_1(X41,X40)
        | ~ m1_pre_topc(X41,X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ v1_tdlat_3(X40)
        | ~ l1_pre_topc(X40) )
      & ( v1_tdlat_3(X41)
        | ~ m1_pre_topc(X41,X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ v1_tdlat_3(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_tdlat_3])])])])])).

fof(c_0_26,plain,(
    ! [X49,X50] :
      ( ( ~ v2_struct_0(esk3_2(X49,X50))
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | v2_struct_0(X49)
        | ~ l1_pre_topc(X49) )
      & ( v1_pre_topc(esk3_2(X49,X50))
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | v2_struct_0(X49)
        | ~ l1_pre_topc(X49) )
      & ( m1_pre_topc(esk3_2(X49,X50),X49)
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | v2_struct_0(X49)
        | ~ l1_pre_topc(X49) )
      & ( X50 = u1_struct_0(esk3_2(X49,X50))
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | v2_struct_0(X49)
        | ~ l1_pre_topc(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).

fof(c_0_27,plain,(
    ! [X57,X58] :
      ( v2_struct_0(X57)
      | ~ v2_pre_topc(X57)
      | ~ l1_pre_topc(X57)
      | ~ v1_xboole_0(X58)
      | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))
      | ~ v3_tex_2(X58,X57) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_tex_2])])])])).

fof(c_0_28,plain,(
    ! [X45,X46] :
      ( ( ~ v1_subset_1(X46,X45)
        | X46 != X45
        | ~ m1_subset_1(X46,k1_zfmisc_1(X45)) )
      & ( X46 = X45
        | v1_subset_1(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X45)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | v1_tops_1(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( v4_pre_topc(X3,X2)
    | ~ v1_borsuk_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_37,plain,(
    ! [X37,X38] :
      ( ~ l1_pre_topc(X37)
      | ~ m1_pre_topc(X38,X37)
      | m1_subset_1(u1_struct_0(X38),k1_zfmisc_1(u1_struct_0(X37))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_38,plain,
    ( v1_borsuk_1(X1,X2)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( m1_pre_topc(esk3_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( v3_tex_2(esk6_0,esk5_0)
    | ~ v1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_42,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_43,plain,(
    ! [X55,X56] :
      ( v2_struct_0(X55)
      | ~ v2_pre_topc(X55)
      | ~ v1_tdlat_3(X55)
      | ~ l1_pre_topc(X55)
      | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
      | v2_tex_2(X56,X55) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).

fof(c_0_44,plain,(
    ! [X18] : m1_subset_1(k2_subset_1(X18),k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_45,plain,(
    ! [X16] : k2_subset_1(X16) = X16 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_46,plain,(
    ! [X43,X44] :
      ( ( ~ v1_tops_1(X44,X43)
        | k2_pre_topc(X43,X44) = u1_struct_0(X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ l1_pre_topc(X43) )
      & ( k2_pre_topc(X43,X44) != u1_struct_0(X43)
        | v1_tops_1(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).

cnf(c_0_47,negated_conjecture,
    ( v1_tops_1(esk6_0,esk5_0)
    | ~ v3_tex_2(esk6_0,esk5_0)
    | ~ v3_pre_topc(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_48,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( v1_tdlat_3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_50,plain,
    ( v4_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v1_borsuk_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( v1_borsuk_1(X1,X2)
    | v2_struct_0(X2)
    | ~ v1_tdlat_3(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_38,c_0_35])).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(esk3_2(esk5_0,esk6_0),esk5_0)
    | v1_xboole_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_30]),c_0_32])]),c_0_33])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_subset_1(esk6_0,u1_struct_0(esk5_0))
    | ~ v1_xboole_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_31]),c_0_32]),c_0_30])]),c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | v1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_30])).

cnf(c_0_56,plain,
    ( X1 = u1_struct_0(esk3_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_59,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_60,plain,(
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

cnf(c_0_61,plain,
    ( k2_pre_topc(X2,X1) = u1_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_62,negated_conjecture,
    ( v1_tops_1(esk6_0,esk5_0)
    | ~ v3_tex_2(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_32]),c_0_30])])).

cnf(c_0_63,plain,
    ( v4_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_borsuk_1(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_50]),c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( v1_borsuk_1(esk3_2(esk5_0,esk6_0),esk5_0)
    | v1_xboole_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_49]),c_0_32])]),c_0_33])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(esk3_2(esk5_0,esk6_0)) = esk6_0
    | v1_xboole_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_30]),c_0_32])]),c_0_33])).

fof(c_0_67,plain,(
    ! [X30] :
      ( ( m1_subset_1(esk2_1(X30),k1_zfmisc_1(u1_struct_0(X30)))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ v1_xboole_0(esk2_1(X30))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( v4_pre_topc(esk2_1(X30),X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).

fof(c_0_68,plain,(
    ! [X61,X62] :
      ( v2_struct_0(X61)
      | ~ v2_pre_topc(X61)
      | ~ l1_pre_topc(X61)
      | ~ m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))
      | ~ v1_tops_1(X62,X61)
      | ~ v2_tex_2(X62,X61)
      | v3_tex_2(X62,X61) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tex_2])])])])).

cnf(c_0_69,plain,
    ( v2_tex_2(X1,X2)
    | v2_struct_0(X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_57,c_0_35])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_71,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_72,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | ~ v3_tex_2(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_32]),c_0_30])])).

cnf(c_0_73,negated_conjecture,
    ( v4_pre_topc(u1_struct_0(esk3_2(esk5_0,esk6_0)),esk5_0)
    | v1_xboole_0(esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_31]),c_0_32])]),c_0_53])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk3_2(esk5_0,esk6_0)) = esk6_0
    | u1_struct_0(esk5_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | v3_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X2,X1)
    | ~ v2_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,plain,
    ( v2_tex_2(u1_struct_0(X1),X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | ~ v3_tex_2(esk6_0,esk5_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_32]),c_0_30])])).

cnf(c_0_79,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | v4_pre_topc(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_65])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk2_1(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_31]),c_0_32])]),c_0_33])).

fof(c_0_81,plain,(
    ! [X24,X25] :
      ( ~ v1_xboole_0(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | ~ v1_subset_1(X25,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).

cnf(c_0_82,plain,
    ( v3_tex_2(u1_struct_0(X1),X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(u1_struct_0(X1),X1)
    | ~ v1_tops_1(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_70])).

cnf(c_0_83,negated_conjecture,
    ( v2_tex_2(u1_struct_0(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_49]),c_0_32])]),c_0_33])).

cnf(c_0_84,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | ~ v3_tex_2(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_86,plain,(
    ! [X22,X23] :
      ( v1_xboole_0(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | v1_subset_1(X23,X22)
      | ~ v1_xboole_0(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_subset_1])])])])).

cnf(c_0_87,negated_conjecture,
    ( v2_tex_2(esk2_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_80]),c_0_49]),c_0_32])]),c_0_33])).

cnf(c_0_88,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk2_1(esk5_0)
    | v1_subset_1(esk2_1(esk5_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_80])).

cnf(c_0_90,plain,
    ( u1_struct_0(esk3_2(X1,u1_struct_0(X1))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_70])).

cnf(c_0_91,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk5_0),esk5_0)
    | ~ v1_tops_1(u1_struct_0(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_92,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_93,negated_conjecture,
    ( v1_subset_1(esk6_0,u1_struct_0(esk5_0))
    | ~ v3_tex_2(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_94,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_41]),c_0_55])).

cnf(c_0_95,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_85]),c_0_70])])).

cnf(c_0_96,plain,
    ( v1_xboole_0(X1)
    | v1_subset_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_97,negated_conjecture,
    ( v3_tex_2(esk2_1(esk5_0),esk5_0)
    | ~ v1_tops_1(esk2_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_80]),c_0_87]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_98,plain,
    ( v4_pre_topc(esk2_1(X1),X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_99,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk2_1(esk5_0)
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_80])])).

cnf(c_0_100,negated_conjecture,
    ( u1_struct_0(esk3_2(esk5_0,u1_struct_0(esk5_0))) = u1_struct_0(esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_32]),c_0_33])).

cnf(c_0_101,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk5_0),esk5_0)
    | k2_pre_topc(esk5_0,u1_struct_0(esk5_0)) != u1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_32]),c_0_70])])).

cnf(c_0_102,negated_conjecture,
    ( ~ v3_tex_2(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94]),c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_xboole_0(esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_30]),c_0_54])).

cnf(c_0_104,negated_conjecture,
    ( v3_tex_2(esk2_1(esk5_0),esk5_0)
    | k2_pre_topc(esk5_0,esk2_1(esk5_0)) != u1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_92]),c_0_32]),c_0_80])])).

cnf(c_0_105,negated_conjecture,
    ( v4_pre_topc(esk2_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_106,negated_conjecture,
    ( u1_struct_0(esk3_2(esk5_0,u1_struct_0(esk5_0))) = u1_struct_0(esk5_0)
    | u1_struct_0(esk5_0) = esk2_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) != esk6_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_94]),c_0_94]),c_0_94]),c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk2_1(esk5_0)
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( v3_tex_2(esk2_1(esk5_0),esk5_0)
    | u1_struct_0(esk5_0) != esk2_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_71]),c_0_105]),c_0_32]),c_0_80])])).

cnf(c_0_110,negated_conjecture,
    ( u1_struct_0(esk3_2(esk5_0,esk6_0)) = esk6_0
    | esk2_1(esk5_0) = esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_94]),c_0_94]),c_0_94])).

cnf(c_0_111,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_71]),c_0_32]),c_0_94]),c_0_70])])).

cnf(c_0_112,negated_conjecture,
    ( esk2_1(esk5_0) = esk6_0
    | ~ v1_xboole_0(esk6_0) ),
    inference(rw,[status(thm)],[c_0_108,c_0_94])).

cnf(c_0_113,negated_conjecture,
    ( v3_tex_2(esk2_1(esk5_0),esk5_0)
    | esk2_1(esk5_0) != esk6_0 ),
    inference(rw,[status(thm)],[c_0_109,c_0_94])).

cnf(c_0_114,negated_conjecture,
    ( esk2_1(esk5_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_110]),c_0_111]),c_0_112])).

cnf(c_0_115,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_114]),c_0_114])]),c_0_102]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:47:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.47  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.030 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(t49_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 0.20/0.47  fof(t47_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_tex_2(X2,X1))=>v1_tops_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 0.20/0.47  fof(t17_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 0.20/0.47  fof(cc1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 0.20/0.47  fof(t11_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_borsuk_1(X2,X1)&m1_pre_topc(X2,X1))<=>v4_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tsep_1)).
% 0.20/0.47  fof(cc5_tdlat_3, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_borsuk_1(X2,X1)&v1_tsep_1(X2,X1))&v1_tdlat_3(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 0.20/0.47  fof(t10_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>?[X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))&X2=u1_struct_0(X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 0.20/0.47  fof(t46_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~(v3_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 0.20/0.47  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.20/0.47  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.20/0.47  fof(t43_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 0.20/0.47  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.47  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.47  fof(d2_tops_3, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 0.20/0.47  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.20/0.47  fof(rc7_pre_topc, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>?[X2]:((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v4_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 0.20/0.47  fof(t48_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v1_tops_1(X2,X1)&v2_tex_2(X2,X1))=>v3_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 0.20/0.47  fof(cc4_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~(v1_subset_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 0.20/0.47  fof(cc2_subset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(~(v1_subset_1(X2,X1))=>~(v1_xboole_0(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_subset_1)).
% 0.20/0.47  fof(c_0_19, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t49_tex_2])).
% 0.20/0.47  fof(c_0_20, plain, ![X59, X60]:(v2_struct_0(X59)|~v2_pre_topc(X59)|~l1_pre_topc(X59)|(~m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))|(~v3_pre_topc(X60,X59)|~v3_tex_2(X60,X59)|v1_tops_1(X60,X59)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).
% 0.20/0.47  fof(c_0_21, negated_conjecture, ((((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&v1_tdlat_3(esk5_0))&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&((~v3_tex_2(esk6_0,esk5_0)|v1_subset_1(esk6_0,u1_struct_0(esk5_0)))&(v3_tex_2(esk6_0,esk5_0)|~v1_subset_1(esk6_0,u1_struct_0(esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.20/0.47  fof(c_0_22, plain, ![X52, X53]:((~v1_tdlat_3(X52)|(~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))|v3_pre_topc(X53,X52))|(~v2_pre_topc(X52)|~l1_pre_topc(X52)))&((m1_subset_1(esk4_1(X52),k1_zfmisc_1(u1_struct_0(X52)))|v1_tdlat_3(X52)|(~v2_pre_topc(X52)|~l1_pre_topc(X52)))&(~v3_pre_topc(esk4_1(X52),X52)|v1_tdlat_3(X52)|(~v2_pre_topc(X52)|~l1_pre_topc(X52))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).
% 0.20/0.47  fof(c_0_23, plain, ![X39]:(~l1_pre_topc(X39)|(~v1_tdlat_3(X39)|v2_pre_topc(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).
% 0.20/0.47  fof(c_0_24, plain, ![X34, X35, X36]:((~v1_borsuk_1(X35,X34)|~m1_pre_topc(X35,X34)|v4_pre_topc(X36,X34)|X36!=u1_struct_0(X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|~m1_pre_topc(X35,X34)|(~v2_pre_topc(X34)|~l1_pre_topc(X34)))&((v1_borsuk_1(X35,X34)|~v4_pre_topc(X36,X34)|X36!=u1_struct_0(X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|~m1_pre_topc(X35,X34)|(~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(m1_pre_topc(X35,X34)|~v4_pre_topc(X36,X34)|X36!=u1_struct_0(X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|~m1_pre_topc(X35,X34)|(~v2_pre_topc(X34)|~l1_pre_topc(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tsep_1])])])])).
% 0.20/0.47  fof(c_0_25, plain, ![X40, X41]:(((v1_borsuk_1(X41,X40)|~m1_pre_topc(X41,X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~v1_tdlat_3(X40)|~l1_pre_topc(X40)))&(v1_tsep_1(X41,X40)|~m1_pre_topc(X41,X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~v1_tdlat_3(X40)|~l1_pre_topc(X40))))&(v1_tdlat_3(X41)|~m1_pre_topc(X41,X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~v1_tdlat_3(X40)|~l1_pre_topc(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_tdlat_3])])])])])).
% 0.20/0.47  fof(c_0_26, plain, ![X49, X50]:((((~v2_struct_0(esk3_2(X49,X50))|(v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49))))|(v2_struct_0(X49)|~l1_pre_topc(X49)))&(v1_pre_topc(esk3_2(X49,X50))|(v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49))))|(v2_struct_0(X49)|~l1_pre_topc(X49))))&(m1_pre_topc(esk3_2(X49,X50),X49)|(v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49))))|(v2_struct_0(X49)|~l1_pre_topc(X49))))&(X50=u1_struct_0(esk3_2(X49,X50))|(v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49))))|(v2_struct_0(X49)|~l1_pre_topc(X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).
% 0.20/0.47  fof(c_0_27, plain, ![X57, X58]:(v2_struct_0(X57)|~v2_pre_topc(X57)|~l1_pre_topc(X57)|(~v1_xboole_0(X58)|~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))|~v3_tex_2(X58,X57))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_tex_2])])])])).
% 0.20/0.47  fof(c_0_28, plain, ![X45, X46]:((~v1_subset_1(X46,X45)|X46!=X45|~m1_subset_1(X46,k1_zfmisc_1(X45)))&(X46=X45|v1_subset_1(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(X45)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.20/0.47  cnf(c_0_29, plain, (v2_struct_0(X1)|v1_tops_1(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.47  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.47  cnf(c_0_31, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.47  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.47  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.47  cnf(c_0_34, plain, (v3_pre_topc(X2,X1)|~v1_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_35, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.47  cnf(c_0_36, plain, (v4_pre_topc(X3,X2)|~v1_borsuk_1(X1,X2)|~m1_pre_topc(X1,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.47  fof(c_0_37, plain, ![X37, X38]:(~l1_pre_topc(X37)|(~m1_pre_topc(X38,X37)|m1_subset_1(u1_struct_0(X38),k1_zfmisc_1(u1_struct_0(X37))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.20/0.47  cnf(c_0_38, plain, (v1_borsuk_1(X1,X2)|v2_struct_0(X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.47  cnf(c_0_39, plain, (m1_pre_topc(esk3_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_40, plain, (v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.47  cnf(c_0_41, negated_conjecture, (v3_tex_2(esk6_0,esk5_0)|~v1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.47  cnf(c_0_42, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.47  fof(c_0_43, plain, ![X55, X56]:(v2_struct_0(X55)|~v2_pre_topc(X55)|~v1_tdlat_3(X55)|~l1_pre_topc(X55)|(~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|v2_tex_2(X56,X55))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).
% 0.20/0.47  fof(c_0_44, plain, ![X18]:m1_subset_1(k2_subset_1(X18),k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.47  fof(c_0_45, plain, ![X16]:k2_subset_1(X16)=X16, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.47  fof(c_0_46, plain, ![X43, X44]:((~v1_tops_1(X44,X43)|k2_pre_topc(X43,X44)=u1_struct_0(X43)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|~l1_pre_topc(X43))&(k2_pre_topc(X43,X44)!=u1_struct_0(X43)|v1_tops_1(X44,X43)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|~l1_pre_topc(X43))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).
% 0.20/0.47  cnf(c_0_47, negated_conjecture, (v1_tops_1(esk6_0,esk5_0)|~v3_tex_2(esk6_0,esk5_0)|~v3_pre_topc(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])]), c_0_33])).
% 0.20/0.47  cnf(c_0_48, plain, (v3_pre_topc(X1,X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.47  cnf(c_0_49, negated_conjecture, (v1_tdlat_3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.47  cnf(c_0_50, plain, (v4_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~v1_borsuk_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[c_0_36])).
% 0.20/0.47  cnf(c_0_51, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.47  cnf(c_0_52, plain, (v1_borsuk_1(X1,X2)|v2_struct_0(X2)|~v1_tdlat_3(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_38, c_0_35])).
% 0.20/0.47  cnf(c_0_53, negated_conjecture, (m1_pre_topc(esk3_2(esk5_0,esk6_0),esk5_0)|v1_xboole_0(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_30]), c_0_32])]), c_0_33])).
% 0.20/0.47  cnf(c_0_54, negated_conjecture, (~v1_subset_1(esk6_0,u1_struct_0(esk5_0))|~v1_xboole_0(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_31]), c_0_32]), c_0_30])]), c_0_33])).
% 0.20/0.47  cnf(c_0_55, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|v1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_42, c_0_30])).
% 0.20/0.47  cnf(c_0_56, plain, (X1=u1_struct_0(esk3_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_57, plain, (v2_struct_0(X1)|v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.47  cnf(c_0_58, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.47  cnf(c_0_59, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.47  fof(c_0_60, plain, ![X32, X33]:((~v4_pre_topc(X33,X32)|k2_pre_topc(X32,X33)=X33|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_pre_topc(X32))&(~v2_pre_topc(X32)|k2_pre_topc(X32,X33)!=X33|v4_pre_topc(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_pre_topc(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.20/0.47  cnf(c_0_61, plain, (k2_pre_topc(X2,X1)=u1_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.47  cnf(c_0_62, negated_conjecture, (v1_tops_1(esk6_0,esk5_0)|~v3_tex_2(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_32]), c_0_30])])).
% 0.20/0.47  cnf(c_0_63, plain, (v4_pre_topc(u1_struct_0(X1),X2)|~v1_borsuk_1(X1,X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_50]), c_0_51])).
% 0.20/0.47  cnf(c_0_64, negated_conjecture, (v1_borsuk_1(esk3_2(esk5_0,esk6_0),esk5_0)|v1_xboole_0(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_49]), c_0_32])]), c_0_33])).
% 0.20/0.47  cnf(c_0_65, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.47  cnf(c_0_66, negated_conjecture, (u1_struct_0(esk3_2(esk5_0,esk6_0))=esk6_0|v1_xboole_0(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_30]), c_0_32])]), c_0_33])).
% 0.20/0.47  fof(c_0_67, plain, ![X30]:(((m1_subset_1(esk2_1(X30),k1_zfmisc_1(u1_struct_0(X30)))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))&(~v1_xboole_0(esk2_1(X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30))))&(v4_pre_topc(esk2_1(X30),X30)|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).
% 0.20/0.47  fof(c_0_68, plain, ![X61, X62]:(v2_struct_0(X61)|~v2_pre_topc(X61)|~l1_pre_topc(X61)|(~m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))|(~v1_tops_1(X62,X61)|~v2_tex_2(X62,X61)|v3_tex_2(X62,X61)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tex_2])])])])).
% 0.20/0.47  cnf(c_0_69, plain, (v2_tex_2(X1,X2)|v2_struct_0(X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_57, c_0_35])).
% 0.20/0.47  cnf(c_0_70, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.47  cnf(c_0_71, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.47  cnf(c_0_72, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|~v3_tex_2(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_32]), c_0_30])])).
% 0.20/0.47  cnf(c_0_73, negated_conjecture, (v4_pre_topc(u1_struct_0(esk3_2(esk5_0,esk6_0)),esk5_0)|v1_xboole_0(esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_31]), c_0_32])]), c_0_53])).
% 0.20/0.47  cnf(c_0_74, negated_conjecture, (u1_struct_0(esk3_2(esk5_0,esk6_0))=esk6_0|u1_struct_0(esk5_0)=esk6_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.47  cnf(c_0_75, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.47  cnf(c_0_76, plain, (v2_struct_0(X1)|v3_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_tops_1(X2,X1)|~v2_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.47  cnf(c_0_77, plain, (v2_tex_2(u1_struct_0(X1),X1)|v2_struct_0(X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.47  cnf(c_0_78, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|~v3_tex_2(esk6_0,esk5_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_32]), c_0_30])])).
% 0.20/0.47  cnf(c_0_79, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|v4_pre_topc(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_65])).
% 0.20/0.47  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk2_1(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_31]), c_0_32])]), c_0_33])).
% 0.20/0.47  fof(c_0_81, plain, ![X24, X25]:(~v1_xboole_0(X24)|(~m1_subset_1(X25,k1_zfmisc_1(X24))|~v1_subset_1(X25,X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).
% 0.20/0.47  cnf(c_0_82, plain, (v3_tex_2(u1_struct_0(X1),X1)|v2_struct_0(X1)|~v2_tex_2(u1_struct_0(X1),X1)|~v1_tops_1(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_76, c_0_70])).
% 0.20/0.47  cnf(c_0_83, negated_conjecture, (v2_tex_2(u1_struct_0(esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_49]), c_0_32])]), c_0_33])).
% 0.20/0.47  cnf(c_0_84, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|~v3_tex_2(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.20/0.47  cnf(c_0_85, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.47  fof(c_0_86, plain, ![X22, X23]:(v1_xboole_0(X22)|(~m1_subset_1(X23,k1_zfmisc_1(X22))|(v1_subset_1(X23,X22)|~v1_xboole_0(X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_subset_1])])])])).
% 0.20/0.47  cnf(c_0_87, negated_conjecture, (v2_tex_2(esk2_1(esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_80]), c_0_49]), c_0_32])]), c_0_33])).
% 0.20/0.47  cnf(c_0_88, plain, (~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.47  cnf(c_0_89, negated_conjecture, (u1_struct_0(esk5_0)=esk2_1(esk5_0)|v1_subset_1(esk2_1(esk5_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_42, c_0_80])).
% 0.20/0.47  cnf(c_0_90, plain, (u1_struct_0(esk3_2(X1,u1_struct_0(X1)))=u1_struct_0(X1)|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_56, c_0_70])).
% 0.20/0.47  cnf(c_0_91, negated_conjecture, (v3_tex_2(u1_struct_0(esk5_0),esk5_0)|~v1_tops_1(u1_struct_0(esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_31]), c_0_32])]), c_0_33])).
% 0.20/0.47  cnf(c_0_92, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.47  cnf(c_0_93, negated_conjecture, (v1_subset_1(esk6_0,u1_struct_0(esk5_0))|~v3_tex_2(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.47  cnf(c_0_94, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_41]), c_0_55])).
% 0.20/0.47  cnf(c_0_95, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_85]), c_0_70])])).
% 0.20/0.47  cnf(c_0_96, plain, (v1_xboole_0(X1)|v1_subset_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.20/0.47  cnf(c_0_97, negated_conjecture, (v3_tex_2(esk2_1(esk5_0),esk5_0)|~v1_tops_1(esk2_1(esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_80]), c_0_87]), c_0_31]), c_0_32])]), c_0_33])).
% 0.20/0.47  cnf(c_0_98, plain, (v4_pre_topc(esk2_1(X1),X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.47  cnf(c_0_99, negated_conjecture, (u1_struct_0(esk5_0)=esk2_1(esk5_0)|~v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_80])])).
% 0.20/0.47  cnf(c_0_100, negated_conjecture, (u1_struct_0(esk3_2(esk5_0,u1_struct_0(esk5_0)))=u1_struct_0(esk5_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_32]), c_0_33])).
% 0.20/0.47  cnf(c_0_101, negated_conjecture, (v3_tex_2(u1_struct_0(esk5_0),esk5_0)|k2_pre_topc(esk5_0,u1_struct_0(esk5_0))!=u1_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_32]), c_0_70])])).
% 0.20/0.47  cnf(c_0_102, negated_conjecture, (~v3_tex_2(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94]), c_0_95])).
% 0.20/0.47  cnf(c_0_103, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|~v1_xboole_0(esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_30]), c_0_54])).
% 0.20/0.47  cnf(c_0_104, negated_conjecture, (v3_tex_2(esk2_1(esk5_0),esk5_0)|k2_pre_topc(esk5_0,esk2_1(esk5_0))!=u1_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_92]), c_0_32]), c_0_80])])).
% 0.20/0.47  cnf(c_0_105, negated_conjecture, (v4_pre_topc(esk2_1(esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_31]), c_0_32])]), c_0_33])).
% 0.20/0.47  cnf(c_0_106, negated_conjecture, (u1_struct_0(esk3_2(esk5_0,u1_struct_0(esk5_0)))=u1_struct_0(esk5_0)|u1_struct_0(esk5_0)=esk2_1(esk5_0)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.20/0.47  cnf(c_0_107, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)!=esk6_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_94]), c_0_94]), c_0_94]), c_0_102])).
% 0.20/0.47  cnf(c_0_108, negated_conjecture, (u1_struct_0(esk5_0)=esk2_1(esk5_0)|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_99, c_0_103])).
% 0.20/0.47  cnf(c_0_109, negated_conjecture, (v3_tex_2(esk2_1(esk5_0),esk5_0)|u1_struct_0(esk5_0)!=esk2_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_71]), c_0_105]), c_0_32]), c_0_80])])).
% 0.20/0.47  cnf(c_0_110, negated_conjecture, (u1_struct_0(esk3_2(esk5_0,esk6_0))=esk6_0|esk2_1(esk5_0)=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_94]), c_0_94]), c_0_94])).
% 0.20/0.47  cnf(c_0_111, negated_conjecture, (~v4_pre_topc(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_71]), c_0_32]), c_0_94]), c_0_70])])).
% 0.20/0.47  cnf(c_0_112, negated_conjecture, (esk2_1(esk5_0)=esk6_0|~v1_xboole_0(esk6_0)), inference(rw,[status(thm)],[c_0_108, c_0_94])).
% 0.20/0.47  cnf(c_0_113, negated_conjecture, (v3_tex_2(esk2_1(esk5_0),esk5_0)|esk2_1(esk5_0)!=esk6_0), inference(rw,[status(thm)],[c_0_109, c_0_94])).
% 0.20/0.47  cnf(c_0_114, negated_conjecture, (esk2_1(esk5_0)=esk6_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_110]), c_0_111]), c_0_112])).
% 0.20/0.47  cnf(c_0_115, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_114]), c_0_114])]), c_0_102]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 116
% 0.20/0.47  # Proof object clause steps            : 77
% 0.20/0.47  # Proof object formula steps           : 39
% 0.20/0.47  # Proof object conjectures             : 48
% 0.20/0.47  # Proof object clause conjectures      : 45
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 29
% 0.20/0.47  # Proof object initial formulas used   : 19
% 0.20/0.47  # Proof object generating inferences   : 35
% 0.20/0.47  # Proof object simplifying inferences  : 102
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 32
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 56
% 0.20/0.47  # Removed in clause preprocessing      : 4
% 0.20/0.47  # Initial clauses in saturation        : 52
% 0.20/0.47  # Processed clauses                    : 1481
% 0.20/0.47  # ...of these trivial                  : 1
% 0.20/0.47  # ...subsumed                          : 983
% 0.20/0.47  # ...remaining for further processing  : 497
% 0.20/0.47  # Other redundant clauses eliminated   : 5
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 8
% 0.20/0.47  # Backward-rewritten                   : 261
% 0.20/0.47  # Generated clauses                    : 2635
% 0.20/0.47  # ...of the previous two non-trivial   : 2514
% 0.20/0.47  # Contextual simplify-reflections      : 60
% 0.20/0.47  # Paramodulations                      : 2628
% 0.20/0.47  # Factorizations                       : 2
% 0.20/0.47  # Equation resolutions                 : 5
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 171
% 0.20/0.47  #    Positive orientable unit clauses  : 20
% 0.20/0.47  #    Positive unorientable unit clauses: 2
% 0.20/0.47  #    Negative unit clauses             : 6
% 0.20/0.47  #    Non-unit-clauses                  : 143
% 0.20/0.47  # Current number of unprocessed clauses: 1049
% 0.20/0.47  # ...number of literals in the above   : 3891
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 324
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 29173
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 12741
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 975
% 0.20/0.47  # Unit Clause-clause subsumption calls : 614
% 0.20/0.47  # Rewrite failures with RHS unbound    : 19
% 0.20/0.47  # BW rewrite match attempts            : 40
% 0.20/0.47  # BW rewrite match successes           : 13
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 39546
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.116 s
% 0.20/0.47  # System time              : 0.008 s
% 0.20/0.47  # Total time               : 0.124 s
% 0.20/0.47  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
