%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1854+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:09 EST 2020

% Result     : Theorem 10.56s
% Output     : CNFRefutation 10.56s
% Verified   : 
% Statistics : Number of formulae       :   18 (  52 expanded)
%              Number of clauses        :   11 (  16 expanded)
%              Number of leaves         :    3 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :   74 ( 232 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ ( v1_tex_2(k1_tex_2(X1,X2),X1)
              & v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tex_2)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

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

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ~ ( v1_tex_2(k1_tex_2(X1,X2),X1)
                & v7_struct_0(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t21_tex_2])).

fof(c_0_4,plain,(
    ! [X11626,X11627] :
      ( ( ~ v2_struct_0(k1_tex_2(X11626,X11627))
        | v2_struct_0(X11626)
        | ~ l1_pre_topc(X11626)
        | ~ m1_subset_1(X11627,u1_struct_0(X11626)) )
      & ( v1_pre_topc(k1_tex_2(X11626,X11627))
        | v2_struct_0(X11626)
        | ~ l1_pre_topc(X11626)
        | ~ m1_subset_1(X11627,u1_struct_0(X11626)) )
      & ( m1_pre_topc(k1_tex_2(X11626,X11627),X11626)
        | v2_struct_0(X11626)
        | ~ l1_pre_topc(X11626)
        | ~ m1_subset_1(X11627,u1_struct_0(X11626)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_5,negated_conjecture,
    ( ~ v2_struct_0(esk1330_0)
    & l1_pre_topc(esk1330_0)
    & m1_subset_1(esk1331_0,u1_struct_0(esk1330_0))
    & v1_tex_2(k1_tex_2(esk1330_0,esk1331_0),esk1330_0)
    & v7_struct_0(esk1330_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

fof(c_0_6,plain,(
    ! [X11566,X11567] :
      ( ( ~ v2_struct_0(X11567)
        | v2_struct_0(X11567)
        | ~ m1_pre_topc(X11567,X11566)
        | v2_struct_0(X11566)
        | ~ v7_struct_0(X11566)
        | ~ l1_pre_topc(X11566) )
      & ( ~ v1_tex_2(X11567,X11566)
        | v2_struct_0(X11567)
        | ~ m1_pre_topc(X11567,X11566)
        | v2_struct_0(X11566)
        | ~ v7_struct_0(X11566)
        | ~ l1_pre_topc(X11566) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).

cnf(c_0_7,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk1331_0,u1_struct_0(esk1330_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( l1_pre_topc(esk1330_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1330_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v7_struct_0(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk1330_0,esk1331_0),esk1330_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk1330_0,esk1331_0),esk1330_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( v7_struct_0(esk1330_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(k1_tex_2(esk1330_0,esk1331_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_9])]),c_0_10]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
