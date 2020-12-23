%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1868+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:09 EST 2020

% Result     : Theorem 34.03s
% Output     : CNFRefutation 34.03s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 167 expanded)
%              Number of clauses        :   26 (  56 expanded)
%              Number of leaves         :    9 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :  218 ( 779 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',dt_m1_pre_topc)).

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',cc1_pre_topc)).

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

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT028+2.ax',t1_tsep_1)).

fof(cc1_tex_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( ( ~ v2_struct_0(X1)
          & v7_struct_0(X1)
          & v2_pre_topc(X1) )
       => ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & v2_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_1)).

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

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t36_tex_2])).

fof(c_0_10,plain,(
    ! [X11697,X11698] :
      ( ( ~ v2_struct_0(k1_tex_2(X11697,X11698))
        | v2_struct_0(X11697)
        | ~ l1_pre_topc(X11697)
        | ~ m1_subset_1(X11698,u1_struct_0(X11697)) )
      & ( v1_pre_topc(k1_tex_2(X11697,X11698))
        | v2_struct_0(X11697)
        | ~ l1_pre_topc(X11697)
        | ~ m1_subset_1(X11698,u1_struct_0(X11697)) )
      & ( m1_pre_topc(k1_tex_2(X11697,X11698),X11697)
        | v2_struct_0(X11697)
        | ~ l1_pre_topc(X11697)
        | ~ m1_subset_1(X11698,u1_struct_0(X11697)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1357_0)
    & v2_pre_topc(esk1357_0)
    & l1_pre_topc(esk1357_0)
    & m1_subset_1(esk1358_0,u1_struct_0(esk1357_0))
    & ~ v2_tex_2(k6_domain_1(u1_struct_0(esk1357_0),esk1358_0),esk1357_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X5918,X5919] :
      ( ~ l1_pre_topc(X5918)
      | ~ m1_pre_topc(X5919,X5918)
      | l1_pre_topc(X5919) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_13,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk1358_0,u1_struct_0(esk1357_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1357_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1357_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X11701,X11702] :
      ( ( ~ v2_struct_0(k1_tex_2(X11701,X11702))
        | v2_struct_0(X11701)
        | ~ l1_pre_topc(X11701)
        | ~ m1_subset_1(X11702,u1_struct_0(X11701)) )
      & ( v7_struct_0(k1_tex_2(X11701,X11702))
        | v2_struct_0(X11701)
        | ~ l1_pre_topc(X11701)
        | ~ m1_subset_1(X11702,u1_struct_0(X11701)) )
      & ( v1_pre_topc(k1_tex_2(X11701,X11702))
        | v2_struct_0(X11701)
        | ~ l1_pre_topc(X11701)
        | ~ m1_subset_1(X11702,u1_struct_0(X11701)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

fof(c_0_18,plain,(
    ! [X5861,X5862] :
      ( ~ v2_pre_topc(X5861)
      | ~ l1_pre_topc(X5861)
      | ~ m1_pre_topc(X5862,X5861)
      | v2_pre_topc(X5862) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_19,plain,(
    ! [X11805,X11806,X11807] :
      ( ( ~ v2_tex_2(X11807,X11805)
        | v1_tdlat_3(X11806)
        | X11807 != u1_struct_0(X11806)
        | ~ m1_subset_1(X11807,k1_zfmisc_1(u1_struct_0(X11805)))
        | v2_struct_0(X11806)
        | ~ m1_pre_topc(X11806,X11805)
        | v2_struct_0(X11805)
        | ~ l1_pre_topc(X11805) )
      & ( ~ v1_tdlat_3(X11806)
        | v2_tex_2(X11807,X11805)
        | X11807 != u1_struct_0(X11806)
        | ~ m1_subset_1(X11807,k1_zfmisc_1(u1_struct_0(X11805)))
        | v2_struct_0(X11806)
        | ~ m1_pre_topc(X11806,X11805)
        | v2_struct_0(X11805)
        | ~ l1_pre_topc(X11805) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

fof(c_0_20,plain,(
    ! [X11076,X11077] :
      ( ~ l1_pre_topc(X11076)
      | ~ m1_pre_topc(X11077,X11076)
      | m1_subset_1(u1_struct_0(X11077),k1_zfmisc_1(u1_struct_0(X11076))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_21,plain,(
    ! [X11598] :
      ( ( ~ v2_struct_0(X11598)
        | v2_struct_0(X11598)
        | ~ v7_struct_0(X11598)
        | ~ v2_pre_topc(X11598)
        | ~ l1_pre_topc(X11598) )
      & ( v2_pre_topc(X11598)
        | v2_struct_0(X11598)
        | ~ v7_struct_0(X11598)
        | ~ v2_pre_topc(X11598)
        | ~ l1_pre_topc(X11598) )
      & ( v1_tdlat_3(X11598)
        | v2_struct_0(X11598)
        | ~ v7_struct_0(X11598)
        | ~ v2_pre_topc(X11598)
        | ~ l1_pre_topc(X11598) )
      & ( v2_tdlat_3(X11598)
        | v2_struct_0(X11598)
        | ~ v7_struct_0(X11598)
        | ~ v2_pre_topc(X11598)
        | ~ l1_pre_topc(X11598) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_tex_1])])])])).

cnf(c_0_22,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk1357_0,esk1358_0),esk1357_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_24,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk1357_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_28,plain,(
    ! [X11680,X11681,X11682] :
      ( ( X11682 != k1_tex_2(X11680,X11681)
        | u1_struct_0(X11682) = k6_domain_1(u1_struct_0(X11680),X11681)
        | v2_struct_0(X11682)
        | ~ v1_pre_topc(X11682)
        | ~ m1_pre_topc(X11682,X11680)
        | ~ m1_subset_1(X11681,u1_struct_0(X11680))
        | v2_struct_0(X11680)
        | ~ l1_pre_topc(X11680) )
      & ( u1_struct_0(X11682) != k6_domain_1(u1_struct_0(X11680),X11681)
        | X11682 = k1_tex_2(X11680,X11681)
        | v2_struct_0(X11682)
        | ~ v1_pre_topc(X11682)
        | ~ m1_pre_topc(X11682,X11680)
        | ~ m1_subset_1(X11681,u1_struct_0(X11680))
        | v2_struct_0(X11680)
        | ~ l1_pre_topc(X11680) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).

cnf(c_0_29,plain,
    ( v2_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(k1_tex_2(esk1357_0,esk1358_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15])])).

cnf(c_0_33,negated_conjecture,
    ( v7_struct_0(k1_tex_2(esk1357_0,esk1358_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(k1_tex_2(esk1357_0,esk1358_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_26]),c_0_15])])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(k1_tex_2(esk1357_0,esk1358_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_36,plain,
    ( u1_struct_0(X1) = k6_domain_1(u1_struct_0(X2),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | X1 != k1_tex_2(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( v1_pre_topc(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,plain,
    ( v2_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v1_tdlat_3(k1_tex_2(esk1357_0,esk1358_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_40,plain,
    ( u1_struct_0(k1_tex_2(X1,X2)) = k6_domain_1(u1_struct_0(X1),X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_37]),c_0_13]),c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( v2_tex_2(u1_struct_0(k1_tex_2(esk1357_0,esk1358_0)),esk1357_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_23]),c_0_39]),c_0_15])]),c_0_35]),c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk1357_0,esk1358_0)) = k6_domain_1(u1_struct_0(esk1357_0),esk1358_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(esk1357_0),esk1358_0),esk1357_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
