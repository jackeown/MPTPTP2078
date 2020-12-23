%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:52 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   77 (1487 expanded)
%              Number of clauses        :   46 ( 457 expanded)
%              Number of leaves         :   15 ( 372 expanded)
%              Depth                    :   16
%              Number of atoms          :  386 (10180 expanded)
%              Number of equality atoms :   29 ( 159 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   31 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).

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

fof(d2_tops_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(t23_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tdlat_3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(t17_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X33,X34] :
      ( v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ v3_pre_topc(X34,X33)
      | ~ v3_tex_2(X34,X33)
      | v1_tops_1(X34,X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v2_pre_topc(esk6_0)
    & v3_tdlat_3(esk6_0)
    & l1_pre_topc(esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    & ( v3_pre_topc(esk7_0,esk6_0)
      | v4_pre_topc(esk7_0,esk6_0) )
    & v3_tex_2(esk7_0,esk6_0)
    & v1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X14,X15] :
      ( ( ~ v1_tops_1(X15,X14)
        | k2_pre_topc(X14,X15) = u1_struct_0(X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( k2_pre_topc(X14,X15) != u1_struct_0(X14)
        | v1_tops_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | v1_tops_1(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v3_tex_2(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X23,X24] :
      ( ( ~ v3_tdlat_3(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v3_pre_topc(X24,X23)
        | v4_pre_topc(X24,X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk3_1(X23),k1_zfmisc_1(u1_struct_0(X23)))
        | v3_tdlat_3(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( v3_pre_topc(esk3_1(X23),X23)
        | v3_tdlat_3(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ v4_pre_topc(esk3_1(X23),X23)
        | v3_tdlat_3(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_tdlat_3])])])])])).

fof(c_0_26,plain,(
    ! [X10,X11] :
      ( ( ~ v4_pre_topc(X11,X10)
        | k2_pre_topc(X10,X11) = X11
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( ~ v2_pre_topc(X10)
        | k2_pre_topc(X10,X11) != X11
        | v4_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_27,plain,
    ( k2_pre_topc(X2,X1) = u1_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( v1_tops_1(esk7_0,esk6_0)
    | ~ v3_pre_topc(esk7_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_29,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk6_0)
    | v4_pre_topc(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( v3_tdlat_3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k2_pre_topc(esk6_0,esk7_0) = u1_struct_0(esk6_0)
    | ~ v3_pre_topc(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_23]),c_0_20])])).

cnf(c_0_34,negated_conjecture,
    ( v4_pre_topc(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_22]),c_0_23]),c_0_20])])).

fof(c_0_35,plain,(
    ! [X26,X27] :
      ( ( ~ v3_tdlat_3(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v4_pre_topc(X27,X26)
        | v3_pre_topc(X27,X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk4_1(X26),k1_zfmisc_1(u1_struct_0(X26)))
        | v3_tdlat_3(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( v4_pre_topc(esk4_1(X26),X26)
        | v3_tdlat_3(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ v3_pre_topc(esk4_1(X26),X26)
        | v3_tdlat_3(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

fof(c_0_36,plain,(
    ! [X29,X30,X31] :
      ( ( ~ v2_tex_2(X30,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ r1_tarski(X31,X30)
        | k9_subset_1(u1_struct_0(X29),X30,k2_pre_topc(X29,X31)) = X31
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_subset_1(esk5_2(X29,X30),k1_zfmisc_1(u1_struct_0(X29)))
        | v2_tex_2(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( r1_tarski(esk5_2(X29,X30),X30)
        | v2_tex_2(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( k9_subset_1(u1_struct_0(X29),X30,k2_pre_topc(X29,esk5_2(X29,X30))) != esk5_2(X29,X30)
        | v2_tex_2(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tex_2])])])])])])).

cnf(c_0_37,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | ~ v3_pre_topc(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_23]),c_0_20])])).

cnf(c_0_38,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( k9_subset_1(u1_struct_0(X2),X1,k2_pre_topc(X2,X3)) = X3
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_31]),c_0_22]),c_0_34]),c_0_23]),c_0_20])])).

fof(c_0_41,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
      | m1_subset_1(k2_pre_topc(X8,X9),k1_zfmisc_1(u1_struct_0(X8))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_42,negated_conjecture,
    ( k9_subset_1(esk7_0,X1,k2_pre_topc(esk6_0,X2)) = X2
    | ~ v2_tex_2(X1,esk6_0)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_43,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( k9_subset_1(esk7_0,X1,X2) = X2
    | ~ v2_tex_2(X1,esk6_0)
    | ~ v4_pre_topc(X2,esk6_0)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_32]),c_0_23]),c_0_40])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk6_0,X1),k1_zfmisc_1(esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_23])])).

fof(c_0_46,plain,(
    ! [X6,X7] :
      ( ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | m1_subset_1(X6,k1_zfmisc_1(X7)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_47,plain,(
    ! [X16,X17,X18] :
      ( ( v2_tex_2(X17,X16)
        | ~ v3_tex_2(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ v2_tex_2(X18,X16)
        | ~ r1_tarski(X17,X18)
        | X17 = X18
        | ~ v3_tex_2(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk1_2(X16,X17),k1_zfmisc_1(u1_struct_0(X16)))
        | ~ v2_tex_2(X17,X16)
        | v3_tex_2(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( v2_tex_2(esk1_2(X16,X17),X16)
        | ~ v2_tex_2(X17,X16)
        | v3_tex_2(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( r1_tarski(X17,esk1_2(X16,X17))
        | ~ v2_tex_2(X17,X16)
        | v3_tex_2(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( X17 != esk1_2(X16,X17)
        | ~ v2_tex_2(X17,X16)
        | v3_tex_2(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

fof(c_0_48,plain,(
    ! [X5] : m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_49,plain,(
    ! [X4] : k2_subset_1(X4) = X4 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_50,negated_conjecture,
    ( k2_pre_topc(esk6_0,X1) = X1
    | ~ v2_tex_2(X2,esk6_0)
    | ~ v4_pre_topc(k2_pre_topc(esk6_0,X1),esk6_0)
    | ~ r1_tarski(k2_pre_topc(esk6_0,X1),X2)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk7_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_44]),c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( v2_tex_2(X1,X2)
    | ~ v3_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k2_pre_topc(esk6_0,X1) = X1
    | ~ v2_tex_2(X2,esk6_0)
    | ~ v4_pre_topc(k2_pre_topc(esk6_0,X1),esk6_0)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(k2_pre_topc(esk6_0,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk7_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( v2_tex_2(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_21]),c_0_23]),c_0_20])])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_59,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | v4_pre_topc(k2_pre_topc(X12,X13),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

fof(c_0_60,plain,(
    ! [X20,X21] :
      ( ( ~ v1_tdlat_3(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | v3_pre_topc(X21,X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk2_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | v1_tdlat_3(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ v3_pre_topc(esk2_1(X20),X20)
        | v1_tdlat_3(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).

fof(c_0_61,plain,(
    ! [X35,X36] :
      ( ( ~ v3_tex_2(X36,X35)
        | ~ v1_subset_1(X36,u1_struct_0(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ v1_tdlat_3(X35)
        | ~ l1_pre_topc(X35) )
      & ( v1_subset_1(X36,u1_struct_0(X35))
        | v3_tex_2(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ v1_tdlat_3(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tex_2])])])])])).

cnf(c_0_62,negated_conjecture,
    ( k2_pre_topc(esk6_0,X1) = X1
    | ~ v4_pre_topc(k2_pre_topc(esk6_0,X1),esk6_0)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_43]),c_0_40]),c_0_56]),c_0_40]),c_0_40]),c_0_57]),c_0_23]),c_0_40])]),c_0_58])).

cnf(c_0_63,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,plain,
    ( v2_struct_0(X2)
    | ~ v3_tex_2(X1,X2)
    | ~ v1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_67,negated_conjecture,
    ( k2_pre_topc(esk6_0,X1) = X1
    | ~ r1_tarski(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_22]),c_0_23]),c_0_40])]),c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( v1_tdlat_3(esk6_0)
    | m1_subset_1(esk2_1(esk6_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_22]),c_0_23])])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_tdlat_3(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_21]),c_0_22]),c_0_23]),c_0_20])]),c_0_24])).

cnf(c_0_70,plain,
    ( v1_tdlat_3(X1)
    | ~ v3_pre_topc(esk2_1(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( k2_pre_topc(esk6_0,X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_51])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk2_1(esk6_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,plain,
    ( v1_tdlat_3(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v4_pre_topc(esk2_1(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_38]),c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( v4_pre_topc(X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_71]),c_0_22]),c_0_23]),c_0_40])])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk2_1(esk6_0),k1_zfmisc_1(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_72,c_0_40])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_31]),c_0_22]),c_0_23]),c_0_75])]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:48:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.029 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t61_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((((v3_pre_topc(X2,X1)|v4_pre_topc(X2,X1))&v3_tex_2(X2,X1))&v1_subset_1(X2,u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 0.13/0.40  fof(t47_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_tex_2(X2,X1))=>v1_tops_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 0.13/0.40  fof(d2_tops_3, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 0.13/0.40  fof(t23_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tdlat_3)).
% 0.13/0.40  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.13/0.40  fof(t24_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 0.13/0.40  fof(t41_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3))=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 0.13/0.40  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.13/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.40  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 0.13/0.40  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.40  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.40  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 0.13/0.40  fof(t17_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 0.13/0.40  fof(t49_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 0.13/0.40  fof(c_0_15, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((((v3_pre_topc(X2,X1)|v4_pre_topc(X2,X1))&v3_tex_2(X2,X1))&v1_subset_1(X2,u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t61_tex_2])).
% 0.13/0.40  fof(c_0_16, plain, ![X33, X34]:(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(~v3_pre_topc(X34,X33)|~v3_tex_2(X34,X33)|v1_tops_1(X34,X33)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).
% 0.13/0.40  fof(c_0_17, negated_conjecture, ((((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&v3_tdlat_3(esk6_0))&l1_pre_topc(esk6_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))&(((v3_pre_topc(esk7_0,esk6_0)|v4_pre_topc(esk7_0,esk6_0))&v3_tex_2(esk7_0,esk6_0))&v1_subset_1(esk7_0,u1_struct_0(esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.13/0.40  fof(c_0_18, plain, ![X14, X15]:((~v1_tops_1(X15,X14)|k2_pre_topc(X14,X15)=u1_struct_0(X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&(k2_pre_topc(X14,X15)!=u1_struct_0(X14)|v1_tops_1(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).
% 0.13/0.40  cnf(c_0_19, plain, (v2_struct_0(X1)|v1_tops_1(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_21, negated_conjecture, (v3_tex_2(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  fof(c_0_25, plain, ![X23, X24]:((~v3_tdlat_3(X23)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|(~v3_pre_topc(X24,X23)|v4_pre_topc(X24,X23)))|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))&((m1_subset_1(esk3_1(X23),k1_zfmisc_1(u1_struct_0(X23)))|v3_tdlat_3(X23)|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))&((v3_pre_topc(esk3_1(X23),X23)|v3_tdlat_3(X23)|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(~v4_pre_topc(esk3_1(X23),X23)|v3_tdlat_3(X23)|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_tdlat_3])])])])])).
% 0.13/0.40  fof(c_0_26, plain, ![X10, X11]:((~v4_pre_topc(X11,X10)|k2_pre_topc(X10,X11)=X11|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))&(~v2_pre_topc(X10)|k2_pre_topc(X10,X11)!=X11|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.13/0.40  cnf(c_0_27, plain, (k2_pre_topc(X2,X1)=u1_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (v1_tops_1(esk7_0,esk6_0)|~v3_pre_topc(esk7_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.13/0.40  cnf(c_0_29, plain, (v4_pre_topc(X2,X1)|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, (v3_pre_topc(esk7_0,esk6_0)|v4_pre_topc(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_31, negated_conjecture, (v3_tdlat_3(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_32, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (k2_pre_topc(esk6_0,esk7_0)=u1_struct_0(esk6_0)|~v3_pre_topc(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_23]), c_0_20])])).
% 0.13/0.40  cnf(c_0_34, negated_conjecture, (v4_pre_topc(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_22]), c_0_23]), c_0_20])])).
% 0.13/0.40  fof(c_0_35, plain, ![X26, X27]:((~v3_tdlat_3(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~v4_pre_topc(X27,X26)|v3_pre_topc(X27,X26)))|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&((m1_subset_1(esk4_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|v3_tdlat_3(X26)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&((v4_pre_topc(esk4_1(X26),X26)|v3_tdlat_3(X26)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~v3_pre_topc(esk4_1(X26),X26)|v3_tdlat_3(X26)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).
% 0.13/0.40  fof(c_0_36, plain, ![X29, X30, X31]:((~v2_tex_2(X30,X29)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|(~r1_tarski(X31,X30)|k9_subset_1(u1_struct_0(X29),X30,k2_pre_topc(X29,X31))=X31))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&((m1_subset_1(esk5_2(X29,X30),k1_zfmisc_1(u1_struct_0(X29)))|v2_tex_2(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&((r1_tarski(esk5_2(X29,X30),X30)|v2_tex_2(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(k9_subset_1(u1_struct_0(X29),X30,k2_pre_topc(X29,esk5_2(X29,X30)))!=esk5_2(X29,X30)|v2_tex_2(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tex_2])])])])])])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|~v3_pre_topc(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_23]), c_0_20])])).
% 0.13/0.40  cnf(c_0_38, plain, (v3_pre_topc(X2,X1)|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.40  cnf(c_0_39, plain, (k9_subset_1(u1_struct_0(X2),X1,k2_pre_topc(X2,X3))=X3|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.40  cnf(c_0_40, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_31]), c_0_22]), c_0_34]), c_0_23]), c_0_20])])).
% 0.13/0.40  fof(c_0_41, plain, ![X8, X9]:(~l1_pre_topc(X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|m1_subset_1(k2_pre_topc(X8,X9),k1_zfmisc_1(u1_struct_0(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (k9_subset_1(esk7_0,X1,k2_pre_topc(esk6_0,X2))=X2|~v2_tex_2(X1,esk6_0)|~r1_tarski(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(esk7_0))|~m1_subset_1(X1,k1_zfmisc_1(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_22]), c_0_23])]), c_0_24])).
% 0.13/0.40  cnf(c_0_43, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (k9_subset_1(esk7_0,X1,X2)=X2|~v2_tex_2(X1,esk6_0)|~v4_pre_topc(X2,esk6_0)|~r1_tarski(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(esk7_0))|~m1_subset_1(X1,k1_zfmisc_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_32]), c_0_23]), c_0_40])])).
% 0.13/0.40  cnf(c_0_45, negated_conjecture, (m1_subset_1(k2_pre_topc(esk6_0,X1),k1_zfmisc_1(esk7_0))|~m1_subset_1(X1,k1_zfmisc_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_40]), c_0_23])])).
% 0.13/0.40  fof(c_0_46, plain, ![X6, X7]:((~m1_subset_1(X6,k1_zfmisc_1(X7))|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|m1_subset_1(X6,k1_zfmisc_1(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.40  fof(c_0_47, plain, ![X16, X17, X18]:(((v2_tex_2(X17,X16)|~v3_tex_2(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))&(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))|(~v2_tex_2(X18,X16)|~r1_tarski(X17,X18)|X17=X18)|~v3_tex_2(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16)))&((m1_subset_1(esk1_2(X16,X17),k1_zfmisc_1(u1_struct_0(X16)))|~v2_tex_2(X17,X16)|v3_tex_2(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))&(((v2_tex_2(esk1_2(X16,X17),X16)|~v2_tex_2(X17,X16)|v3_tex_2(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))&(r1_tarski(X17,esk1_2(X16,X17))|~v2_tex_2(X17,X16)|v3_tex_2(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16)))&(X17!=esk1_2(X16,X17)|~v2_tex_2(X17,X16)|v3_tex_2(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 0.13/0.40  fof(c_0_48, plain, ![X5]:m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.40  fof(c_0_49, plain, ![X4]:k2_subset_1(X4)=X4, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.40  cnf(c_0_50, negated_conjecture, (k2_pre_topc(esk6_0,X1)=X1|~v2_tex_2(X2,esk6_0)|~v4_pre_topc(k2_pre_topc(esk6_0,X1),esk6_0)|~r1_tarski(k2_pre_topc(esk6_0,X1),X2)|~r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(esk7_0))|~m1_subset_1(X2,k1_zfmisc_1(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_44]), c_0_45])).
% 0.13/0.40  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.40  cnf(c_0_52, plain, (v2_tex_2(X1,X2)|~v3_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.40  cnf(c_0_53, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.40  cnf(c_0_54, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (k2_pre_topc(esk6_0,X1)=X1|~v2_tex_2(X2,esk6_0)|~v4_pre_topc(k2_pre_topc(esk6_0,X1),esk6_0)|~r1_tarski(X1,X2)|~m1_subset_1(k2_pre_topc(esk6_0,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(esk7_0))|~m1_subset_1(X2,k1_zfmisc_1(esk7_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (v2_tex_2(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_21]), c_0_23]), c_0_20])])).
% 0.13/0.40  cnf(c_0_57, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.13/0.40  cnf(c_0_58, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.40  fof(c_0_59, plain, ![X12, X13]:(~v2_pre_topc(X12)|~l1_pre_topc(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|v4_pre_topc(k2_pre_topc(X12,X13),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 0.13/0.40  fof(c_0_60, plain, ![X20, X21]:((~v1_tdlat_3(X20)|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|v3_pre_topc(X21,X20))|(~v2_pre_topc(X20)|~l1_pre_topc(X20)))&((m1_subset_1(esk2_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|v1_tdlat_3(X20)|(~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~v3_pre_topc(esk2_1(X20),X20)|v1_tdlat_3(X20)|(~v2_pre_topc(X20)|~l1_pre_topc(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).
% 0.13/0.40  fof(c_0_61, plain, ![X35, X36]:((~v3_tex_2(X36,X35)|~v1_subset_1(X36,u1_struct_0(X35))|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~v1_tdlat_3(X35)|~l1_pre_topc(X35)))&(v1_subset_1(X36,u1_struct_0(X35))|v3_tex_2(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~v1_tdlat_3(X35)|~l1_pre_topc(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tex_2])])])])])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (k2_pre_topc(esk6_0,X1)=X1|~v4_pre_topc(k2_pre_topc(esk6_0,X1),esk6_0)|~r1_tarski(X1,esk7_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_43]), c_0_40]), c_0_56]), c_0_40]), c_0_40]), c_0_57]), c_0_23]), c_0_40])]), c_0_58])).
% 0.13/0.40  cnf(c_0_63, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.40  cnf(c_0_64, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v1_tdlat_3(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.40  cnf(c_0_65, plain, (v2_struct_0(X2)|~v3_tex_2(X1,X2)|~v1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_67, negated_conjecture, (k2_pre_topc(esk6_0,X1)=X1|~r1_tarski(X1,esk7_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_22]), c_0_23]), c_0_40])]), c_0_58])).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (v1_tdlat_3(esk6_0)|m1_subset_1(esk2_1(esk6_0),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_22]), c_0_23])])).
% 0.13/0.40  cnf(c_0_69, negated_conjecture, (~v1_tdlat_3(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_21]), c_0_22]), c_0_23]), c_0_20])]), c_0_24])).
% 0.13/0.40  cnf(c_0_70, plain, (v1_tdlat_3(X1)|~v3_pre_topc(esk2_1(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.40  cnf(c_0_71, negated_conjecture, (k2_pre_topc(esk6_0,X1)=X1|~m1_subset_1(X1,k1_zfmisc_1(esk7_0))), inference(spm,[status(thm)],[c_0_67, c_0_51])).
% 0.13/0.40  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk2_1(esk6_0),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(sr,[status(thm)],[c_0_68, c_0_69])).
% 0.13/0.40  cnf(c_0_73, plain, (v1_tdlat_3(X1)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)|~v4_pre_topc(esk2_1(X1),X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_38]), c_0_64])).
% 0.13/0.40  cnf(c_0_74, negated_conjecture, (v4_pre_topc(X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_71]), c_0_22]), c_0_23]), c_0_40])])).
% 0.13/0.40  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk2_1(esk6_0),k1_zfmisc_1(esk7_0))), inference(rw,[status(thm)],[c_0_72, c_0_40])).
% 0.13/0.40  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_31]), c_0_22]), c_0_23]), c_0_75])]), c_0_69]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 77
% 0.13/0.40  # Proof object clause steps            : 46
% 0.13/0.40  # Proof object formula steps           : 31
% 0.13/0.40  # Proof object conjectures             : 31
% 0.13/0.40  # Proof object clause conjectures      : 28
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 24
% 0.13/0.40  # Proof object initial formulas used   : 15
% 0.13/0.40  # Proof object generating inferences   : 19
% 0.13/0.40  # Proof object simplifying inferences  : 72
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 15
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 42
% 0.13/0.40  # Removed in clause preprocessing      : 1
% 0.13/0.40  # Initial clauses in saturation        : 41
% 0.13/0.40  # Processed clauses                    : 211
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 38
% 0.13/0.40  # ...remaining for further processing  : 173
% 0.13/0.40  # Other redundant clauses eliminated   : 1
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 7
% 0.13/0.40  # Backward-rewritten                   : 10
% 0.13/0.40  # Generated clauses                    : 316
% 0.13/0.40  # ...of the previous two non-trivial   : 240
% 0.13/0.40  # Contextual simplify-reflections      : 8
% 0.13/0.40  # Paramodulations                      : 314
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
% 0.13/0.40  # Current number of processed clauses  : 114
% 0.13/0.40  #    Positive orientable unit clauses  : 12
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 2
% 0.13/0.40  #    Non-unit-clauses                  : 100
% 0.13/0.40  # Current number of unprocessed clauses: 106
% 0.13/0.40  # ...number of literals in the above   : 485
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 60
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 2056
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 452
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 44
% 0.13/0.40  # Unit Clause-clause subsumption calls : 42
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 6
% 0.13/0.40  # BW rewrite match successes           : 4
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 13210
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.047 s
% 0.13/0.40  # System time              : 0.003 s
% 0.13/0.40  # Total time               : 0.050 s
% 0.13/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
