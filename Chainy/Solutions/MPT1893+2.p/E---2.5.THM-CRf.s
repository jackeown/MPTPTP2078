%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1893+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:09 EST 2020

% Result     : Theorem 14.38s
% Output     : CNFRefutation 14.38s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 482 expanded)
%              Number of clauses        :   46 ( 159 expanded)
%              Number of leaves         :   18 ( 120 expanded)
%              Depth                    :   10
%              Number of atoms          :  290 (2969 expanded)
%              Number of equality atoms :   27 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   18 (   2 average)
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

fof(fc1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_subset_1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ~ v1_xboole_0(k3_subset_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

fof(cc4_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ~ v1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',cc4_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',dt_k3_subset_1)).

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

fof(t30_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT019+2.ax',t30_tops_1)).

fof(cc6_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v3_pre_topc(X2,X1)
              & v3_tops_1(X2,X1) )
           => v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT019+2.ax',cc6_tops_1)).

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
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',t52_pre_topc)).

fof(t93_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v2_tops_1(X2,X1)
              & v4_pre_topc(X2,X1) )
           => v3_tops_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT019+2.ax',t93_tops_1)).

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

fof(dt_k1_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',dt_k1_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',d3_subset_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',d4_subset_1)).

fof(d4_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT019+2.ax',d4_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',involutiveness_k3_subset_1)).

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,plain,(
    ! [X11717,X11718] :
      ( v1_xboole_0(X11717)
      | ~ v1_subset_1(X11718,X11717)
      | ~ m1_subset_1(X11718,k1_zfmisc_1(X11717))
      | ~ v1_xboole_0(k3_subset_1(X11717,X11718)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_tex_2])])])).

fof(c_0_20,plain,(
    ! [X1844,X1845] :
      ( ~ v1_xboole_0(X1844)
      | ~ m1_subset_1(X1845,k1_zfmisc_1(X1844))
      | ~ v1_subset_1(X1845,X1844) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).

fof(c_0_21,plain,(
    ! [X1584,X1585] :
      ( ~ m1_subset_1(X1585,k1_zfmisc_1(X1584))
      | m1_subset_1(k3_subset_1(X1584,X1585),k1_zfmisc_1(X1584)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk1375_0)
    & v2_pre_topc(esk1375_0)
    & v3_tdlat_3(esk1375_0)
    & l1_pre_topc(esk1375_0)
    & m1_subset_1(esk1376_0,k1_zfmisc_1(u1_struct_0(esk1375_0)))
    & ( v3_pre_topc(esk1376_0,esk1375_0)
      | v4_pre_topc(esk1376_0,esk1375_0) )
    & v3_tex_2(esk1376_0,esk1375_0)
    & v1_subset_1(esk1376_0,u1_struct_0(esk1375_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_23,plain,(
    ! [X11833,X11834] :
      ( ( ~ v3_tdlat_3(X11833)
        | ~ m1_subset_1(X11834,k1_zfmisc_1(u1_struct_0(X11833)))
        | ~ v4_pre_topc(X11834,X11833)
        | v3_pre_topc(X11834,X11833)
        | ~ v2_pre_topc(X11833)
        | ~ l1_pre_topc(X11833) )
      & ( m1_subset_1(esk1357_1(X11833),k1_zfmisc_1(u1_struct_0(X11833)))
        | v3_tdlat_3(X11833)
        | ~ v2_pre_topc(X11833)
        | ~ l1_pre_topc(X11833) )
      & ( v4_pre_topc(esk1357_1(X11833),X11833)
        | v3_tdlat_3(X11833)
        | ~ v2_pre_topc(X11833)
        | ~ l1_pre_topc(X11833) )
      & ( ~ v3_pre_topc(esk1357_1(X11833),X11833)
        | v3_tdlat_3(X11833)
        | ~ v2_pre_topc(X11833)
        | ~ l1_pre_topc(X11833) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k3_subset_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk1376_0,k1_zfmisc_1(u1_struct_0(esk1375_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X6865,X6866] :
      ( ( ~ v3_pre_topc(X6866,X6865)
        | v4_pre_topc(k3_subset_1(u1_struct_0(X6865),X6866),X6865)
        | ~ m1_subset_1(X6866,k1_zfmisc_1(u1_struct_0(X6865)))
        | ~ l1_pre_topc(X6865) )
      & ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X6865),X6866),X6865)
        | v3_pre_topc(X6866,X6865)
        | ~ m1_subset_1(X6866,k1_zfmisc_1(u1_struct_0(X6865)))
        | ~ l1_pre_topc(X6865) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).

cnf(c_0_29,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v3_tdlat_3(esk1375_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( v2_pre_topc(esk1375_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk1375_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( v3_pre_topc(esk1376_0,esk1375_0)
    | v4_pre_topc(esk1376_0,esk1375_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X6744,X6745] :
      ( ~ v2_pre_topc(X6744)
      | ~ l1_pre_topc(X6744)
      | ~ m1_subset_1(X6745,k1_zfmisc_1(u1_struct_0(X6744)))
      | ~ v3_pre_topc(X6745,X6744)
      | ~ v3_tops_1(X6745,X6744)
      | v1_xboole_0(X6745) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc6_tops_1])])])).

cnf(c_0_35,plain,
    ( ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(k3_subset_1(X2,X1)) ),
    inference(csr,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( v1_subset_1(esk1376_0,u1_struct_0(esk1375_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1375_0),esk1376_0),k1_zfmisc_1(u1_struct_0(esk1375_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_38,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( v3_pre_topc(esk1376_0,esk1375_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_27]),c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

fof(c_0_40,plain,(
    ! [X11827,X11828] :
      ( ( ~ v3_tdlat_3(X11827)
        | ~ m1_subset_1(X11828,k1_zfmisc_1(u1_struct_0(X11827)))
        | ~ v3_pre_topc(X11828,X11827)
        | v4_pre_topc(X11828,X11827)
        | ~ v2_pre_topc(X11827)
        | ~ l1_pre_topc(X11827) )
      & ( m1_subset_1(esk1355_1(X11827),k1_zfmisc_1(u1_struct_0(X11827)))
        | v3_tdlat_3(X11827)
        | ~ v2_pre_topc(X11827)
        | ~ l1_pre_topc(X11827) )
      & ( v3_pre_topc(esk1355_1(X11827),X11827)
        | v3_tdlat_3(X11827)
        | ~ v2_pre_topc(X11827)
        | ~ l1_pre_topc(X11827) )
      & ( ~ v4_pre_topc(esk1355_1(X11827),X11827)
        | v3_tdlat_3(X11827)
        | ~ v2_pre_topc(X11827)
        | ~ l1_pre_topc(X11827) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_tdlat_3])])])])])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_tops_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(esk1375_0),esk1376_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_36])])).

cnf(c_0_43,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk1375_0),esk1376_0),esk1375_0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(esk1375_0),esk1376_0),esk1375_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_37]),c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_44,negated_conjecture,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(esk1375_0),esk1376_0),esk1375_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_27]),c_0_39]),c_0_32])])).

fof(c_0_45,plain,(
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

fof(c_0_46,plain,(
    ! [X6044,X6045] :
      ( ( ~ v4_pre_topc(X6045,X6044)
        | k2_pre_topc(X6044,X6045) = X6045
        | ~ m1_subset_1(X6045,k1_zfmisc_1(u1_struct_0(X6044)))
        | ~ l1_pre_topc(X6044) )
      & ( ~ v2_pre_topc(X6044)
        | k2_pre_topc(X6044,X6045) != X6045
        | v4_pre_topc(X6045,X6044)
        | ~ m1_subset_1(X6045,k1_zfmisc_1(u1_struct_0(X6044)))
        | ~ l1_pre_topc(X6044) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_47,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_48,plain,(
    ! [X7015,X7016] :
      ( ~ l1_pre_topc(X7015)
      | ~ m1_subset_1(X7016,k1_zfmisc_1(u1_struct_0(X7015)))
      | ~ v2_tops_1(X7016,X7015)
      | ~ v4_pre_topc(X7016,X7015)
      | v3_tops_1(X7016,X7015) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t93_tops_1])])])).

cnf(c_0_49,negated_conjecture,
    ( ~ v3_tops_1(k3_subset_1(u1_struct_0(esk1375_0),esk1376_0),esk1375_0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(esk1375_0),esk1376_0),esk1375_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_37]),c_0_31]),c_0_32])]),c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk1375_0),esk1376_0),esk1375_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_51,plain,
    ( k2_pre_topc(X2,X1) = u1_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( v4_pre_topc(esk1376_0,esk1375_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_27]),c_0_30]),c_0_39]),c_0_31]),c_0_32])])).

fof(c_0_54,plain,(
    ! [X11912,X11913] :
      ( v2_struct_0(X11912)
      | ~ v2_pre_topc(X11912)
      | ~ l1_pre_topc(X11912)
      | ~ m1_subset_1(X11913,k1_zfmisc_1(u1_struct_0(X11912)))
      | ~ v3_pre_topc(X11913,X11912)
      | ~ v3_tex_2(X11913,X11912)
      | v1_tops_1(X11913,X11912) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).

fof(c_0_55,plain,(
    ! [X1582] : m1_subset_1(k1_subset_1(X1582),k1_zfmisc_1(X1582)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

fof(c_0_56,plain,(
    ! [X1521] : k1_subset_1(X1521) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_57,plain,(
    ! [X1699] : k2_subset_1(X1699) = k3_subset_1(X1699,k1_subset_1(X1699)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_58,plain,(
    ! [X1539] : k2_subset_1(X1539) = X1539 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_59,plain,(
    ! [X6752,X6753] :
      ( ( ~ v2_tops_1(X6753,X6752)
        | v1_tops_1(k3_subset_1(u1_struct_0(X6752),X6753),X6752)
        | ~ m1_subset_1(X6753,k1_zfmisc_1(u1_struct_0(X6752)))
        | ~ l1_pre_topc(X6752) )
      & ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X6752),X6753),X6752)
        | v2_tops_1(X6753,X6752)
        | ~ m1_subset_1(X6753,k1_zfmisc_1(u1_struct_0(X6752)))
        | ~ l1_pre_topc(X6752) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).

cnf(c_0_60,plain,
    ( v3_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tops_1(X2,X1)
    | ~ v4_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( ~ v3_tops_1(k3_subset_1(u1_struct_0(esk1375_0),esk1376_0),esk1375_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_62,negated_conjecture,
    ( k2_pre_topc(esk1375_0,esk1376_0) = u1_struct_0(esk1375_0)
    | ~ v1_tops_1(esk1376_0,esk1375_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_27]),c_0_32])])).

cnf(c_0_63,negated_conjecture,
    ( k2_pre_topc(esk1375_0,esk1376_0) = esk1376_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_27]),c_0_53]),c_0_32])])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | v1_tops_1(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( v3_tex_2(esk1376_0,esk1375_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_66,negated_conjecture,
    ( ~ v2_struct_0(esk1375_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_67,plain,(
    ! [X1650,X1651] :
      ( ~ m1_subset_1(X1651,k1_zfmisc_1(X1650))
      | k3_subset_1(X1650,k3_subset_1(X1650,X1651)) = X1651 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_68,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_69,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_70,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_71,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,plain,
    ( v2_tops_1(X2,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( ~ v2_tops_1(k3_subset_1(u1_struct_0(esk1375_0),esk1376_0),esk1375_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_37]),c_0_44]),c_0_32])]),c_0_61])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk1375_0) = esk1376_0
    | ~ v1_tops_1(esk1376_0,esk1375_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( v1_tops_1(esk1376_0,esk1375_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_27]),c_0_65]),c_0_39]),c_0_31]),c_0_32])]),c_0_66])).

cnf(c_0_76,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_78,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1375_0),k3_subset_1(u1_struct_0(esk1375_0),esk1376_0)),esk1375_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_37]),c_0_32])]),c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(esk1375_0) = esk1376_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])])).

cnf(c_0_81,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_80]),c_0_81]),c_0_78]),c_0_75])]),
    [proof]).
%------------------------------------------------------------------------------
