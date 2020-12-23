%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1895+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:09 EST 2020

% Result     : Theorem 12.47s
% Output     : CNFRefutation 12.47s
% Verified   : 
% Statistics : Number of formulae       :   23 (  69 expanded)
%              Number of clauses        :   14 (  21 expanded)
%              Number of leaves         :    4 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   88 ( 368 expanded)
%              Number of equality atoms :   13 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
           => k3_tarski(a_2_0_tex_2(X1,X2)) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tex_2)).

fof(d2_tops_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(t62_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
           => v1_tops_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tex_2)).

fof(t54_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k3_tarski(a_2_0_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tex_2)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_tex_2(X2,X1)
             => k3_tarski(a_2_0_tex_2(X1,X2)) = u1_struct_0(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t63_tex_2])).

fof(c_0_5,plain,(
    ! [X11677,X11678] :
      ( ( ~ v1_tops_1(X11678,X11677)
        | k2_pre_topc(X11677,X11678) = u1_struct_0(X11677)
        | ~ m1_subset_1(X11678,k1_zfmisc_1(u1_struct_0(X11677)))
        | ~ l1_pre_topc(X11677) )
      & ( k2_pre_topc(X11677,X11678) != u1_struct_0(X11677)
        | v1_tops_1(X11678,X11677)
        | ~ m1_subset_1(X11678,k1_zfmisc_1(u1_struct_0(X11677)))
        | ~ l1_pre_topc(X11677) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk1375_0)
    & v2_pre_topc(esk1375_0)
    & v3_tdlat_3(esk1375_0)
    & l1_pre_topc(esk1375_0)
    & m1_subset_1(esk1376_0,k1_zfmisc_1(u1_struct_0(esk1375_0)))
    & v3_tex_2(esk1376_0,esk1375_0)
    & k3_tarski(a_2_0_tex_2(esk1375_0,esk1376_0)) != u1_struct_0(esk1375_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X11961,X11962] :
      ( v2_struct_0(X11961)
      | ~ v2_pre_topc(X11961)
      | ~ v3_tdlat_3(X11961)
      | ~ l1_pre_topc(X11961)
      | ~ m1_subset_1(X11962,k1_zfmisc_1(u1_struct_0(X11961)))
      | ~ v3_tex_2(X11962,X11961)
      | v1_tops_1(X11962,X11961) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_tex_2])])])])).

cnf(c_0_8,plain,
    ( k2_pre_topc(X2,X1) = u1_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk1376_0,k1_zfmisc_1(u1_struct_0(esk1375_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk1375_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | v1_tops_1(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v3_tex_2(esk1376_0,esk1375_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( v3_tdlat_3(esk1375_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk1375_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1375_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_16,plain,(
    ! [X11932,X11933] :
      ( v2_struct_0(X11932)
      | ~ v2_pre_topc(X11932)
      | ~ v3_tdlat_3(X11932)
      | ~ l1_pre_topc(X11932)
      | ~ m1_subset_1(X11933,k1_zfmisc_1(u1_struct_0(X11932)))
      | k2_pre_topc(X11932,X11933) = k3_tarski(a_2_0_tex_2(X11932,X11933)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t54_tex_2])])])])).

cnf(c_0_17,negated_conjecture,
    ( k2_pre_topc(esk1375_0,esk1376_0) = u1_struct_0(esk1375_0)
    | ~ v1_tops_1(esk1376_0,esk1375_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_18,negated_conjecture,
    ( v1_tops_1(esk1376_0,esk1375_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_9]),c_0_12]),c_0_13]),c_0_14]),c_0_10])]),c_0_15])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | k2_pre_topc(X1,X2) = k3_tarski(a_2_0_tex_2(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k2_pre_topc(esk1375_0,esk1376_0) = u1_struct_0(esk1375_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_21,negated_conjecture,
    ( k3_tarski(a_2_0_tex_2(esk1375_0,esk1376_0)) != u1_struct_0(esk1375_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_9]),c_0_20]),c_0_13]),c_0_14]),c_0_10])]),c_0_21]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
