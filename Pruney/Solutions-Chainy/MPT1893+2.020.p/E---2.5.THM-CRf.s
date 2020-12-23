%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:52 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   77 (2326 expanded)
%              Number of clauses        :   48 ( 713 expanded)
%              Number of leaves         :   14 ( 582 expanded)
%              Depth                    :   18
%              Number of atoms          :  437 (16063 expanded)
%              Number of equality atoms :   36 ( 271 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ~ ( ( v3_pre_topc(X2,X1)
                | v4_pre_topc(X2,X1) )
              & v3_tex_2(X2,X1)
              & v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

fof(t24_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

fof(d2_tops_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

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

fof(t23_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).

fof(t41_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r1_tarski(X3,X2)
                 => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(d5_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( r1_tarski(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = X3 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

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

fof(t49_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
          <=> ~ v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ~ ( ( v3_pre_topc(X2,X1)
                  | v4_pre_topc(X2,X1) )
                & v3_tex_2(X2,X1)
                & v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t61_tex_2])).

fof(c_0_15,plain,(
    ! [X29,X30] :
      ( ( ~ v3_tdlat_3(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v4_pre_topc(X30,X29)
        | v3_pre_topc(X30,X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_subset_1(esk7_1(X29),k1_zfmisc_1(u1_struct_0(X29)))
        | v3_tdlat_3(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v4_pre_topc(esk7_1(X29),X29)
        | v3_tdlat_3(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( ~ v3_pre_topc(esk7_1(X29),X29)
        | v3_tdlat_3(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk9_0)
    & v2_pre_topc(esk9_0)
    & v3_tdlat_3(esk9_0)
    & l1_pre_topc(esk9_0)
    & m1_subset_1(esk10_0,k1_zfmisc_1(u1_struct_0(esk9_0)))
    & ( v3_pre_topc(esk10_0,esk9_0)
      | v4_pre_topc(esk10_0,esk9_0) )
    & v3_tex_2(esk10_0,esk9_0)
    & v1_subset_1(esk10_0,u1_struct_0(esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X36,X37] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | ~ v3_pre_topc(X37,X36)
      | ~ v3_tex_2(X37,X36)
      | v1_tops_1(X37,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).

cnf(c_0_18,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v3_pre_topc(esk10_0,esk9_0)
    | v4_pre_topc(esk10_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v3_tdlat_3(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(u1_struct_0(esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X11,X12] :
      ( ( ~ v1_tops_1(X12,X11)
        | k2_pre_topc(X11,X12) = u1_struct_0(X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) )
      & ( k2_pre_topc(X11,X12) != u1_struct_0(X11)
        | v1_tops_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | v1_tops_1(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v3_tex_2(esk10_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( v3_pre_topc(esk10_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_29,plain,(
    ! [X9,X10] :
      ( ( ~ v4_pre_topc(X10,X9)
        | k2_pre_topc(X9,X10) = X10
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) )
      & ( ~ v2_pre_topc(X9)
        | k2_pre_topc(X9,X10) != X10
        | v4_pre_topc(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_30,plain,
    ( k2_pre_topc(X2,X1) = u1_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( v1_tops_1(esk10_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_26]),c_0_27]),c_0_21]),c_0_22])]),c_0_28])).

cnf(c_0_32,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k2_pre_topc(esk9_0,esk10_0) = u1_struct_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_22]),c_0_23])])).

fof(c_0_34,plain,(
    ! [X26,X27] :
      ( ( ~ v3_tdlat_3(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v3_pre_topc(X27,X26)
        | v4_pre_topc(X27,X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk6_1(X26),k1_zfmisc_1(u1_struct_0(X26)))
        | v3_tdlat_3(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( v3_pre_topc(esk6_1(X26),X26)
        | v3_tdlat_3(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ v4_pre_topc(esk6_1(X26),X26)
        | v3_tdlat_3(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_tdlat_3])])])])])).

fof(c_0_35,plain,(
    ! [X32,X33,X34] :
      ( ( ~ v2_tex_2(X33,X32)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ r1_tarski(X34,X33)
        | k9_subset_1(u1_struct_0(X32),X33,k2_pre_topc(X32,X34)) = X34
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( m1_subset_1(esk8_2(X32,X33),k1_zfmisc_1(u1_struct_0(X32)))
        | v2_tex_2(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( r1_tarski(esk8_2(X32,X33),X33)
        | v2_tex_2(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( k9_subset_1(u1_struct_0(X32),X33,k2_pre_topc(X32,esk8_2(X32,X33))) != esk8_2(X32,X33)
        | v2_tex_2(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tex_2])])])])])])).

cnf(c_0_36,negated_conjecture,
    ( u1_struct_0(esk9_0) = esk10_0
    | ~ v4_pre_topc(esk10_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_22]),c_0_23])])).

cnf(c_0_37,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( k9_subset_1(u1_struct_0(X2),X1,k2_pre_topc(X2,X3)) = X3
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( u1_struct_0(esk9_0) = esk10_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_20]),c_0_27]),c_0_21]),c_0_22]),c_0_23])])).

fof(c_0_40,plain,(
    ! [X13,X14,X15,X18] :
      ( ( m1_subset_1(esk1_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r1_tarski(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( v3_pre_topc(esk1_3(X13,X14,X15),X13)
        | ~ r1_tarski(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( k9_subset_1(u1_struct_0(X13),X14,esk1_3(X13,X14,X15)) = X15
        | ~ r1_tarski(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk2_2(X13,X14),k1_zfmisc_1(u1_struct_0(X13)))
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( r1_tarski(esk2_2(X13,X14),X14)
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ v3_pre_topc(X18,X13)
        | k9_subset_1(u1_struct_0(X13),X14,X18) != esk2_2(X13,X14)
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).

cnf(c_0_41,negated_conjecture,
    ( k9_subset_1(esk10_0,X1,k2_pre_topc(esk9_0,X2)) = X2
    | ~ v2_tex_2(X1,esk9_0)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk10_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_21]),c_0_22])]),c_0_28])).

cnf(c_0_42,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( k9_subset_1(esk10_0,X1,X2) = X2
    | ~ v2_tex_2(X1,esk9_0)
    | ~ v4_pre_topc(X2,esk9_0)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk10_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_32]),c_0_22]),c_0_39])])).

cnf(c_0_45,negated_conjecture,
    ( k9_subset_1(esk10_0,X1,esk1_3(esk9_0,X1,X2)) = X2
    | ~ v2_tex_2(X1,esk9_0)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk10_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_39]),c_0_22])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk1_3(esk9_0,X1,X2),k1_zfmisc_1(esk10_0))
    | ~ v2_tex_2(X1,esk9_0)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk10_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_39]),c_0_22])])).

cnf(c_0_47,negated_conjecture,
    ( esk1_3(esk9_0,X1,X2) = X2
    | ~ v2_tex_2(X1,esk9_0)
    | ~ v4_pre_topc(esk1_3(esk9_0,X1,X2),esk9_0)
    | ~ r1_tarski(esk1_3(esk9_0,X1,X2),X1)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk10_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk10_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_48,negated_conjecture,
    ( esk1_3(esk9_0,X1,X2) = X2
    | ~ v3_pre_topc(esk1_3(esk9_0,X1,X2),esk9_0)
    | ~ v2_tex_2(X1,esk9_0)
    | ~ r1_tarski(esk1_3(esk9_0,X1,X2),X1)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk10_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk10_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_37]),c_0_20]),c_0_21]),c_0_22]),c_0_39])]),c_0_46])).

cnf(c_0_49,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_50,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_51,plain,(
    ! [X19,X20,X21] :
      ( ( v2_tex_2(X20,X19)
        | ~ v3_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ v2_tex_2(X21,X19)
        | ~ r1_tarski(X20,X21)
        | X20 = X21
        | ~ v3_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk3_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ v2_tex_2(X20,X19)
        | v3_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( v2_tex_2(esk3_2(X19,X20),X19)
        | ~ v2_tex_2(X20,X19)
        | v3_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( r1_tarski(X20,esk3_2(X19,X20))
        | ~ v2_tex_2(X20,X19)
        | v3_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( X20 != esk3_2(X19,X20)
        | ~ v2_tex_2(X20,X19)
        | v3_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

fof(c_0_52,plain,(
    ! [X6] : m1_subset_1(k2_subset_1(X6),k1_zfmisc_1(X6)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_53,plain,(
    ! [X5] : k2_subset_1(X5) = X5 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_54,negated_conjecture,
    ( esk1_3(esk9_0,X1,X2) = X2
    | ~ v2_tex_2(X1,esk9_0)
    | ~ r1_tarski(esk1_3(esk9_0,X1,X2),X1)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk10_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_22]),c_0_39]),c_0_39])])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( v2_tex_2(X1,X2)
    | ~ v3_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_59,plain,(
    ! [X23] :
      ( ( m1_subset_1(esk4_1(X23),k1_zfmisc_1(u1_struct_0(X23)))
        | v1_tdlat_3(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk5_1(X23),u1_struct_0(X23))
        | v1_tdlat_3(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( esk4_1(X23) = k1_tarski(esk5_1(X23))
        | v1_tdlat_3(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ v3_pre_topc(esk4_1(X23),X23)
        | v1_tdlat_3(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_tdlat_3])])])])).

fof(c_0_60,plain,(
    ! [X38,X39] :
      ( ( ~ v3_tex_2(X39,X38)
        | ~ v1_subset_1(X39,u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ v1_tdlat_3(X38)
        | ~ l1_pre_topc(X38) )
      & ( v1_subset_1(X39,u1_struct_0(X38))
        | v3_tex_2(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ v1_tdlat_3(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tex_2])])])])])).

cnf(c_0_61,negated_conjecture,
    ( esk1_3(esk9_0,X1,X2) = X2
    | ~ v2_tex_2(X1,esk9_0)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(esk1_3(esk9_0,X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk10_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( v2_tex_2(esk10_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_26]),c_0_22]),c_0_23])])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( m1_subset_1(esk4_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( v2_struct_0(X2)
    | ~ v3_tex_2(X1,X2)
    | ~ v1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( v1_subset_1(esk10_0,u1_struct_0(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_68,negated_conjecture,
    ( esk1_3(esk9_0,esk10_0,X1) = X1
    | ~ r1_tarski(X1,esk10_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_43]),c_0_39]),c_0_39]),c_0_62]),c_0_39]),c_0_39]),c_0_63]),c_0_22]),c_0_39]),c_0_39]),c_0_39]),c_0_63])]),c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( v1_tdlat_3(esk9_0)
    | m1_subset_1(esk4_1(esk9_0),k1_zfmisc_1(u1_struct_0(esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_21]),c_0_22])])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_tdlat_3(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_26]),c_0_21]),c_0_22]),c_0_23])]),c_0_28])).

cnf(c_0_71,plain,
    ( v1_tdlat_3(X1)
    | ~ v3_pre_topc(esk4_1(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,negated_conjecture,
    ( v3_pre_topc(X1,esk9_0)
    | ~ r1_tarski(X1,esk10_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_68]),c_0_62]),c_0_22]),c_0_39]),c_0_39]),c_0_63])]),c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk4_1(esk9_0),k1_zfmisc_1(u1_struct_0(esk9_0))) ),
    inference(sr,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tarski(esk4_1(esk9_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_21]),c_0_22])]),c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk4_1(esk9_0),k1_zfmisc_1(esk10_0)) ),
    inference(rw,[status(thm)],[c_0_73,c_0_39])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_55]),c_0_75])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.033 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t61_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((((v3_pre_topc(X2,X1)|v4_pre_topc(X2,X1))&v3_tex_2(X2,X1))&v1_subset_1(X2,u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tex_2)).
% 0.13/0.40  fof(t24_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 0.13/0.40  fof(t47_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_tex_2(X2,X1))=>v1_tops_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 0.13/0.40  fof(d2_tops_3, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 0.13/0.40  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.13/0.40  fof(t23_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tdlat_3)).
% 0.13/0.40  fof(t41_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3))=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 0.13/0.40  fof(d5_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 0.13/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.40  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 0.13/0.40  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.40  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.40  fof(t19_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k1_tarski(X3)=>v3_pre_topc(X2,X1))))=>v1_tdlat_3(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tdlat_3)).
% 0.13/0.40  fof(t49_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 0.13/0.40  fof(c_0_14, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((((v3_pre_topc(X2,X1)|v4_pre_topc(X2,X1))&v3_tex_2(X2,X1))&v1_subset_1(X2,u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t61_tex_2])).
% 0.13/0.40  fof(c_0_15, plain, ![X29, X30]:((~v3_tdlat_3(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~v4_pre_topc(X30,X29)|v3_pre_topc(X30,X29)))|(~v2_pre_topc(X29)|~l1_pre_topc(X29)))&((m1_subset_1(esk7_1(X29),k1_zfmisc_1(u1_struct_0(X29)))|v3_tdlat_3(X29)|(~v2_pre_topc(X29)|~l1_pre_topc(X29)))&((v4_pre_topc(esk7_1(X29),X29)|v3_tdlat_3(X29)|(~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(~v3_pre_topc(esk7_1(X29),X29)|v3_tdlat_3(X29)|(~v2_pre_topc(X29)|~l1_pre_topc(X29)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).
% 0.13/0.40  fof(c_0_16, negated_conjecture, ((((~v2_struct_0(esk9_0)&v2_pre_topc(esk9_0))&v3_tdlat_3(esk9_0))&l1_pre_topc(esk9_0))&(m1_subset_1(esk10_0,k1_zfmisc_1(u1_struct_0(esk9_0)))&(((v3_pre_topc(esk10_0,esk9_0)|v4_pre_topc(esk10_0,esk9_0))&v3_tex_2(esk10_0,esk9_0))&v1_subset_1(esk10_0,u1_struct_0(esk9_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.13/0.40  fof(c_0_17, plain, ![X36, X37]:(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(~v3_pre_topc(X37,X36)|~v3_tex_2(X37,X36)|v1_tops_1(X37,X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).
% 0.13/0.40  cnf(c_0_18, plain, (v3_pre_topc(X2,X1)|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_19, negated_conjecture, (v3_pre_topc(esk10_0,esk9_0)|v4_pre_topc(esk10_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_20, negated_conjecture, (v3_tdlat_3(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_21, negated_conjecture, (v2_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(u1_struct_0(esk9_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  fof(c_0_24, plain, ![X11, X12]:((~v1_tops_1(X12,X11)|k2_pre_topc(X11,X12)=u1_struct_0(X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|~l1_pre_topc(X11))&(k2_pre_topc(X11,X12)!=u1_struct_0(X11)|v1_tops_1(X12,X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|~l1_pre_topc(X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).
% 0.13/0.40  cnf(c_0_25, plain, (v2_struct_0(X1)|v1_tops_1(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_26, negated_conjecture, (v3_tex_2(esk10_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_27, negated_conjecture, (v3_pre_topc(esk10_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  fof(c_0_29, plain, ![X9, X10]:((~v4_pre_topc(X10,X9)|k2_pre_topc(X9,X10)=X10|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~l1_pre_topc(X9))&(~v2_pre_topc(X9)|k2_pre_topc(X9,X10)!=X10|v4_pre_topc(X10,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~l1_pre_topc(X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.13/0.40  cnf(c_0_30, plain, (k2_pre_topc(X2,X1)=u1_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_31, negated_conjecture, (v1_tops_1(esk10_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_23]), c_0_26]), c_0_27]), c_0_21]), c_0_22])]), c_0_28])).
% 0.13/0.40  cnf(c_0_32, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (k2_pre_topc(esk9_0,esk10_0)=u1_struct_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_22]), c_0_23])])).
% 0.13/0.40  fof(c_0_34, plain, ![X26, X27]:((~v3_tdlat_3(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~v3_pre_topc(X27,X26)|v4_pre_topc(X27,X26)))|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&((m1_subset_1(esk6_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|v3_tdlat_3(X26)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&((v3_pre_topc(esk6_1(X26),X26)|v3_tdlat_3(X26)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~v4_pre_topc(esk6_1(X26),X26)|v3_tdlat_3(X26)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_tdlat_3])])])])])).
% 0.13/0.40  fof(c_0_35, plain, ![X32, X33, X34]:((~v2_tex_2(X33,X32)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|(~r1_tarski(X34,X33)|k9_subset_1(u1_struct_0(X32),X33,k2_pre_topc(X32,X34))=X34))|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&((m1_subset_1(esk8_2(X32,X33),k1_zfmisc_1(u1_struct_0(X32)))|v2_tex_2(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&((r1_tarski(esk8_2(X32,X33),X33)|v2_tex_2(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(k9_subset_1(u1_struct_0(X32),X33,k2_pre_topc(X32,esk8_2(X32,X33)))!=esk8_2(X32,X33)|v2_tex_2(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tex_2])])])])])])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (u1_struct_0(esk9_0)=esk10_0|~v4_pre_topc(esk10_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_22]), c_0_23])])).
% 0.13/0.40  cnf(c_0_37, plain, (v4_pre_topc(X2,X1)|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.40  cnf(c_0_38, plain, (k9_subset_1(u1_struct_0(X2),X1,k2_pre_topc(X2,X3))=X3|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.40  cnf(c_0_39, negated_conjecture, (u1_struct_0(esk9_0)=esk10_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_20]), c_0_27]), c_0_21]), c_0_22]), c_0_23])])).
% 0.13/0.40  fof(c_0_40, plain, ![X13, X14, X15, X18]:(((m1_subset_1(esk1_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(X13)))|~r1_tarski(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))|~v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))&((v3_pre_topc(esk1_3(X13,X14,X15),X13)|~r1_tarski(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))|~v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))&(k9_subset_1(u1_struct_0(X13),X14,esk1_3(X13,X14,X15))=X15|~r1_tarski(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))|~v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))))&((m1_subset_1(esk2_2(X13,X14),k1_zfmisc_1(u1_struct_0(X13)))|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))&((r1_tarski(esk2_2(X13,X14),X14)|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))&(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X13)))|(~v3_pre_topc(X18,X13)|k9_subset_1(u1_struct_0(X13),X14,X18)!=esk2_2(X13,X14))|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (k9_subset_1(esk10_0,X1,k2_pre_topc(esk9_0,X2))=X2|~v2_tex_2(X1,esk9_0)|~r1_tarski(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(esk10_0))|~m1_subset_1(X1,k1_zfmisc_1(esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_21]), c_0_22])]), c_0_28])).
% 0.13/0.40  cnf(c_0_42, plain, (k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3))=X3|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.40  cnf(c_0_43, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (k9_subset_1(esk10_0,X1,X2)=X2|~v2_tex_2(X1,esk9_0)|~v4_pre_topc(X2,esk9_0)|~r1_tarski(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(esk10_0))|~m1_subset_1(X1,k1_zfmisc_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_32]), c_0_22]), c_0_39])])).
% 0.13/0.40  cnf(c_0_45, negated_conjecture, (k9_subset_1(esk10_0,X1,esk1_3(esk9_0,X1,X2))=X2|~v2_tex_2(X1,esk9_0)|~r1_tarski(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(esk10_0))|~m1_subset_1(X1,k1_zfmisc_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_39]), c_0_22])])).
% 0.13/0.40  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk1_3(esk9_0,X1,X2),k1_zfmisc_1(esk10_0))|~v2_tex_2(X1,esk9_0)|~r1_tarski(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(esk10_0))|~m1_subset_1(X1,k1_zfmisc_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_39]), c_0_22])])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (esk1_3(esk9_0,X1,X2)=X2|~v2_tex_2(X1,esk9_0)|~v4_pre_topc(esk1_3(esk9_0,X1,X2),esk9_0)|~r1_tarski(esk1_3(esk9_0,X1,X2),X1)|~r1_tarski(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(esk10_0))|~m1_subset_1(X2,k1_zfmisc_1(esk10_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.13/0.40  cnf(c_0_48, negated_conjecture, (esk1_3(esk9_0,X1,X2)=X2|~v3_pre_topc(esk1_3(esk9_0,X1,X2),esk9_0)|~v2_tex_2(X1,esk9_0)|~r1_tarski(esk1_3(esk9_0,X1,X2),X1)|~r1_tarski(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(esk10_0))|~m1_subset_1(X2,k1_zfmisc_1(esk10_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_37]), c_0_20]), c_0_21]), c_0_22]), c_0_39])]), c_0_46])).
% 0.13/0.40  cnf(c_0_49, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X1)|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.40  fof(c_0_50, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.40  fof(c_0_51, plain, ![X19, X20, X21]:(((v2_tex_2(X20,X19)|~v3_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|(~v2_tex_2(X21,X19)|~r1_tarski(X20,X21)|X20=X21)|~v3_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19)))&((m1_subset_1(esk3_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))|~v2_tex_2(X20,X19)|v3_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(((v2_tex_2(esk3_2(X19,X20),X19)|~v2_tex_2(X20,X19)|v3_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(r1_tarski(X20,esk3_2(X19,X20))|~v2_tex_2(X20,X19)|v3_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19)))&(X20!=esk3_2(X19,X20)|~v2_tex_2(X20,X19)|v3_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 0.13/0.40  fof(c_0_52, plain, ![X6]:m1_subset_1(k2_subset_1(X6),k1_zfmisc_1(X6)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.40  fof(c_0_53, plain, ![X5]:k2_subset_1(X5)=X5, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (esk1_3(esk9_0,X1,X2)=X2|~v2_tex_2(X1,esk9_0)|~r1_tarski(esk1_3(esk9_0,X1,X2),X1)|~r1_tarski(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(esk10_0))|~m1_subset_1(X2,k1_zfmisc_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_22]), c_0_39]), c_0_39])])).
% 0.13/0.40  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.40  cnf(c_0_56, plain, (v2_tex_2(X1,X2)|~v3_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.40  cnf(c_0_57, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.40  cnf(c_0_58, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.40  fof(c_0_59, plain, ![X23]:((m1_subset_1(esk4_1(X23),k1_zfmisc_1(u1_struct_0(X23)))|v1_tdlat_3(X23)|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))&((m1_subset_1(esk5_1(X23),u1_struct_0(X23))|v1_tdlat_3(X23)|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))&((esk4_1(X23)=k1_tarski(esk5_1(X23))|v1_tdlat_3(X23)|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(~v3_pre_topc(esk4_1(X23),X23)|v1_tdlat_3(X23)|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_tdlat_3])])])])).
% 0.13/0.40  fof(c_0_60, plain, ![X38, X39]:((~v3_tex_2(X39,X38)|~v1_subset_1(X39,u1_struct_0(X38))|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~v1_tdlat_3(X38)|~l1_pre_topc(X38)))&(v1_subset_1(X39,u1_struct_0(X38))|v3_tex_2(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~v1_tdlat_3(X38)|~l1_pre_topc(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tex_2])])])])])).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (esk1_3(esk9_0,X1,X2)=X2|~v2_tex_2(X1,esk9_0)|~r1_tarski(X2,X1)|~m1_subset_1(esk1_3(esk9_0,X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(esk10_0))|~m1_subset_1(X2,k1_zfmisc_1(esk10_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (v2_tex_2(esk10_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_26]), c_0_22]), c_0_23])])).
% 0.13/0.40  cnf(c_0_63, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.13/0.40  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.40  cnf(c_0_65, plain, (m1_subset_1(esk4_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v1_tdlat_3(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.40  cnf(c_0_66, plain, (v2_struct_0(X2)|~v3_tex_2(X1,X2)|~v1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.40  cnf(c_0_67, negated_conjecture, (v1_subset_1(esk10_0,u1_struct_0(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (esk1_3(esk9_0,esk10_0,X1)=X1|~r1_tarski(X1,esk10_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_43]), c_0_39]), c_0_39]), c_0_62]), c_0_39]), c_0_39]), c_0_63]), c_0_22]), c_0_39]), c_0_39]), c_0_39]), c_0_63])]), c_0_64])).
% 0.13/0.40  cnf(c_0_69, negated_conjecture, (v1_tdlat_3(esk9_0)|m1_subset_1(esk4_1(esk9_0),k1_zfmisc_1(u1_struct_0(esk9_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_70, negated_conjecture, (~v1_tdlat_3(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_26]), c_0_21]), c_0_22]), c_0_23])]), c_0_28])).
% 0.13/0.40  cnf(c_0_71, plain, (v1_tdlat_3(X1)|~v3_pre_topc(esk4_1(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.40  cnf(c_0_72, negated_conjecture, (v3_pre_topc(X1,esk9_0)|~r1_tarski(X1,esk10_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_68]), c_0_62]), c_0_22]), c_0_39]), c_0_39]), c_0_63])]), c_0_64])).
% 0.13/0.40  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk4_1(esk9_0),k1_zfmisc_1(u1_struct_0(esk9_0)))), inference(sr,[status(thm)],[c_0_69, c_0_70])).
% 0.13/0.40  cnf(c_0_74, negated_conjecture, (~r1_tarski(esk4_1(esk9_0),esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_21]), c_0_22])]), c_0_70])).
% 0.13/0.40  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk4_1(esk9_0),k1_zfmisc_1(esk10_0))), inference(rw,[status(thm)],[c_0_73, c_0_39])).
% 0.13/0.40  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_55]), c_0_75])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 77
% 0.13/0.40  # Proof object clause steps            : 48
% 0.13/0.40  # Proof object formula steps           : 29
% 0.13/0.40  # Proof object conjectures             : 33
% 0.13/0.40  # Proof object clause conjectures      : 30
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 25
% 0.13/0.40  # Proof object initial formulas used   : 14
% 0.13/0.40  # Proof object generating inferences   : 20
% 0.13/0.40  # Proof object simplifying inferences  : 85
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 14
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 47
% 0.13/0.40  # Removed in clause preprocessing      : 1
% 0.13/0.40  # Initial clauses in saturation        : 46
% 0.13/0.40  # Processed clauses                    : 199
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 6
% 0.13/0.40  # ...remaining for further processing  : 193
% 0.13/0.40  # Other redundant clauses eliminated   : 1
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 4
% 0.13/0.40  # Backward-rewritten                   : 7
% 0.13/0.40  # Generated clauses                    : 267
% 0.13/0.40  # ...of the previous two non-trivial   : 221
% 0.13/0.40  # Contextual simplify-reflections      : 7
% 0.13/0.40  # Paramodulations                      : 263
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 1
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 133
% 0.13/0.40  #    Positive orientable unit clauses  : 15
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 3
% 0.13/0.40  #    Non-unit-clauses                  : 115
% 0.13/0.40  # Current number of unprocessed clauses: 111
% 0.13/0.40  # ...number of literals in the above   : 648
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 61
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 2130
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 481
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 15
% 0.13/0.40  # Unit Clause-clause subsumption calls : 30
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 3
% 0.13/0.40  # BW rewrite match successes           : 2
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 13501
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.048 s
% 0.13/0.40  # System time              : 0.007 s
% 0.13/0.40  # Total time               : 0.056 s
% 0.13/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
