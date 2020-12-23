%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:23 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  110 (2560 expanded)
%              Number of clauses        :   75 (1007 expanded)
%              Number of leaves         :   17 ( 626 expanded)
%              Depth                    :   20
%              Number of atoms          :  337 (9375 expanded)
%              Number of equality atoms :   29 (1146 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & v2_tdlat_3(X1) )
           => v2_tdlat_3(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tex_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

fof(cc2_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(d2_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_tdlat_3(X1)
      <=> u1_pre_topc(X1) = k2_tarski(k1_xboole_0,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tdlat_3)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t78_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> r1_tarski(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(t35_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v1_tops_2(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
                   => ( X4 = X2
                     => v1_tops_2(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).

fof(t31_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
             => m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & v2_tdlat_3(X1) )
             => v2_tdlat_3(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_tex_2])).

fof(c_0_18,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_19,plain,(
    ! [X14,X15] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X14),u1_pre_topc(X14)))
      | m1_pre_topc(X15,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

fof(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & l1_pre_topc(esk2_0)
    & g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    & v2_tdlat_3(esk1_0)
    & ~ v2_tdlat_3(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_21,plain,(
    ! [X16,X17] :
      ( ( ~ m1_pre_topc(X16,X17)
        | m1_pre_topc(X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( ~ m1_pre_topc(X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
        | m1_pre_topc(X16,X17)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_22,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(X12,X11)
      | l1_pre_topc(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_23,plain,(
    ! [X32,X33,X34] :
      ( ( ~ r1_tarski(u1_struct_0(X33),u1_struct_0(X34))
        | m1_pre_topc(X33,X34)
        | ~ m1_pre_topc(X34,X32)
        | ~ m1_pre_topc(X33,X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ m1_pre_topc(X33,X34)
        | r1_tarski(u1_struct_0(X33),u1_struct_0(X34))
        | ~ m1_pre_topc(X34,X32)
        | ~ m1_pre_topc(X33,X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_33,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( m1_pre_topc(X1,X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

fof(c_0_37,plain,(
    ! [X35] :
      ( ~ l1_pre_topc(X35)
      | ~ v2_tdlat_3(X35)
      | v2_pre_topc(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_26]),c_0_27])])).

fof(c_0_39,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | m1_pre_topc(X29,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_40,plain,(
    ! [X27,X28] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)))
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)),X27)
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(X1,X1)
    | ~ v2_pre_topc(esk1_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_27])])).

cnf(c_0_42,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( v2_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_38]),c_0_34])])).

cnf(c_0_45,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_36]),c_0_27])])).

cnf(c_0_47,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_27])])).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_27])])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_34])])).

fof(c_0_51,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | r1_tarski(u1_struct_0(X31),u1_struct_0(X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

cnf(c_0_52,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ m1_pre_topc(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_26])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0))
    | ~ v2_pre_topc(esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_27])])).

cnf(c_0_58,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_49])])).

cnf(c_0_59,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_42]),c_0_43]),c_0_27])])).

cnf(c_0_61,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_38]),c_0_58])])).

fof(c_0_62,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_63,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | m1_subset_1(u1_pre_topc(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

fof(c_0_65,plain,(
    ! [X36] :
      ( ( ~ v2_tdlat_3(X36)
        | u1_pre_topc(X36) = k2_tarski(k1_xboole_0,u1_struct_0(X36))
        | ~ l1_pre_topc(X36) )
      & ( u1_pre_topc(X36) != k2_tarski(k1_xboole_0,u1_struct_0(X36))
        | v2_tdlat_3(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tdlat_3])])])).

fof(c_0_66,plain,(
    ! [X7,X8] : k1_enumset1(X7,X7,X8) = k2_tarski(X7,X8) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_67,plain,(
    ! [X25,X26] :
      ( ( ~ v1_tops_2(X26,X25)
        | r1_tarski(X26,u1_pre_topc(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ l1_pre_topc(X25) )
      & ( ~ r1_tarski(X26,u1_pre_topc(X25))
        | v1_tops_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_tops_2])])])])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(esk2_0)
    | ~ m1_pre_topc(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_49])).

cnf(c_0_71,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_45]),c_0_34])])).

cnf(c_0_72,plain,
    ( u1_pre_topc(X1) = k2_tarski(k1_xboole_0,u1_struct_0(X1))
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_74,plain,(
    ! [X21,X22,X23,X24] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
      | ~ m1_pre_topc(X23,X21)
      | ~ v1_tops_2(X22,X21)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
      | X24 != X22
      | v1_tops_2(X24,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_2])])])).

fof(c_0_75,plain,(
    ! [X18,X19,X20] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
      | m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_2])])])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,u1_pre_topc(X2))
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_78,plain,
    ( r1_tarski(u1_pre_topc(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_36]),c_0_71])])).

cnf(c_0_80,plain,
    ( v2_tdlat_3(X1)
    | u1_pre_topc(X1) != k2_tarski(k1_xboole_0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_81,plain,
    ( u1_pre_topc(X1) = k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_82,plain,
    ( v1_tops_2(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,plain,
    ( v1_tops_2(X1,X2)
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,u1_pre_topc(X2))
    | ~ v1_tops_2(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk1_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_27])])).

cnf(c_0_87,plain,
    ( v2_tdlat_3(X1)
    | u1_pre_topc(X1) != k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_80,c_0_73])).

cnf(c_0_88,negated_conjecture,
    ( k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(esk2_0)) = u1_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_79]),c_0_43]),c_0_27])])).

cnf(c_0_89,negated_conjecture,
    ( ~ v2_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_90,plain,
    ( v1_tops_2(X1,X2)
    | ~ v1_tops_2(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_82]),c_0_83])).

cnf(c_0_91,plain,
    ( v1_tops_2(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_77])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk1_0),u1_pre_topc(esk2_0))
    | ~ v1_tops_2(u1_pre_topc(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_34])])).

cnf(c_0_93,negated_conjecture,
    ( u1_pre_topc(esk1_0) != u1_pre_topc(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_34])]),c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(X1,u1_pre_topc(esk1_0))
    | ~ v1_tops_2(X1,esk1_0)
    | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_79]),c_0_27])])).

cnf(c_0_95,plain,
    ( v1_tops_2(X1,X2)
    | ~ v1_tops_2(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_77])).

cnf(c_0_96,negated_conjecture,
    ( v1_tops_2(X1,esk1_0)
    | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_79]),c_0_27])])).

cnf(c_0_97,negated_conjecture,
    ( ~ v1_tops_2(u1_pre_topc(esk1_0),esk2_0)
    | ~ r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_92]),c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk1_0))
    | ~ v1_tops_2(u1_pre_topc(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_78]),c_0_34])])).

cnf(c_0_99,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk1_0),esk2_0)
    | ~ v1_tops_2(u1_pre_topc(esk1_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_86])).

cnf(c_0_100,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_86]),c_0_31])])).

cnf(c_0_101,negated_conjecture,
    ( v1_tops_2(X1,esk1_0)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_pre_topc(esk1_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_79])).

cnf(c_0_102,negated_conjecture,
    ( ~ v1_tops_2(u1_pre_topc(esk1_0),esk2_0)
    | ~ v1_tops_2(u1_pre_topc(esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk1_0),esk2_0)
    | ~ m1_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_27])])).

cnf(c_0_104,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk2_0),esk1_0)
    | ~ v1_tops_2(u1_pre_topc(esk2_0),X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_78]),c_0_34])])).

cnf(c_0_105,plain,
    ( v1_tops_2(u1_pre_topc(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_69]),c_0_31])])).

cnf(c_0_106,negated_conjecture,
    ( ~ v1_tops_2(u1_pre_topc(esk2_0),esk1_0)
    | ~ m1_pre_topc(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_49]),c_0_34])])).

cnf(c_0_108,negated_conjecture,
    ( ~ m1_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_107])])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_36]),c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.018 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t18_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v2_tdlat_3(X1))=>v2_tdlat_3(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tex_2)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.13/0.38  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.13/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.38  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.13/0.38  fof(cc2_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 0.13/0.38  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.13/0.38  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 0.13/0.38  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.13/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.38  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.13/0.38  fof(d2_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_tdlat_3(X1)<=>u1_pre_topc(X1)=k2_tarski(k1_xboole_0,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tdlat_3)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t78_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>r1_tarski(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 0.13/0.38  fof(t35_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_pre_topc(X3,X1)=>(v1_tops_2(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))=>(X4=X2=>v1_tops_2(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_2)).
% 0.13/0.38  fof(t31_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))=>m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 0.13/0.38  fof(c_0_17, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v2_tdlat_3(X1))=>v2_tdlat_3(X2))))), inference(assume_negation,[status(cth)],[t18_tex_2])).
% 0.13/0.38  fof(c_0_18, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  fof(c_0_19, plain, ![X14, X15]:(~l1_pre_topc(X14)|(~m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X14),u1_pre_topc(X14)))|m1_pre_topc(X15,X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.13/0.38  fof(c_0_20, negated_conjecture, (l1_pre_topc(esk1_0)&(l1_pre_topc(esk2_0)&((g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))&v2_tdlat_3(esk1_0))&~v2_tdlat_3(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.13/0.38  fof(c_0_21, plain, ![X16, X17]:((~m1_pre_topc(X16,X17)|m1_pre_topc(X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))|~l1_pre_topc(X17)|~l1_pre_topc(X16))&(~m1_pre_topc(X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))|m1_pre_topc(X16,X17)|~l1_pre_topc(X17)|~l1_pre_topc(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.13/0.38  fof(c_0_22, plain, ![X11, X12]:(~l1_pre_topc(X11)|(~m1_pre_topc(X12,X11)|l1_pre_topc(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.38  fof(c_0_23, plain, ![X32, X33, X34]:((~r1_tarski(u1_struct_0(X33),u1_struct_0(X34))|m1_pre_topc(X33,X34)|~m1_pre_topc(X34,X32)|~m1_pre_topc(X33,X32)|(~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(~m1_pre_topc(X33,X34)|r1_tarski(u1_struct_0(X33),u1_struct_0(X34))|~m1_pre_topc(X34,X32)|~m1_pre_topc(X33,X32)|(~v2_pre_topc(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.13/0.38  cnf(c_0_24, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_25, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_28, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_29, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_30, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.13/0.38  cnf(c_0_33, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_35, plain, (m1_pre_topc(X1,X1)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.13/0.38  fof(c_0_37, plain, ![X35]:(~l1_pre_topc(X35)|(~v2_tdlat_3(X35)|v2_pre_topc(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_26]), c_0_27])])).
% 0.13/0.38  fof(c_0_39, plain, ![X29]:(~l1_pre_topc(X29)|m1_pre_topc(X29,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.13/0.38  fof(c_0_40, plain, ![X27, X28]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)))|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)),X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (m1_pre_topc(X1,X1)|~v2_pre_topc(esk1_0)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_27])])).
% 0.13/0.38  cnf(c_0_42, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (v2_tdlat_3(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_38]), c_0_34])])).
% 0.13/0.38  cnf(c_0_45, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_36]), c_0_27])])).
% 0.13/0.38  cnf(c_0_47, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_27])])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (m1_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_27])])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_34])])).
% 0.13/0.38  fof(c_0_51, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_pre_topc(X31,X30)|r1_tarski(u1_struct_0(X31),u1_struct_0(X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.13/0.38  cnf(c_0_52, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~m1_pre_topc(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_26])).
% 0.13/0.38  cnf(c_0_55, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_56, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0))|~v2_pre_topc(esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_27])])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_49])])).
% 0.13/0.38  cnf(c_0_59, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0))|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_42]), c_0_43]), c_0_27])])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_38]), c_0_58])])).
% 0.13/0.38  fof(c_0_62, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.38  fof(c_0_63, plain, ![X13]:(~l1_pre_topc(X13)|m1_subset_1(u1_pre_topc(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (u1_struct_0(X1)=u1_struct_0(esk1_0)|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.13/0.38  fof(c_0_65, plain, ![X36]:((~v2_tdlat_3(X36)|u1_pre_topc(X36)=k2_tarski(k1_xboole_0,u1_struct_0(X36))|~l1_pre_topc(X36))&(u1_pre_topc(X36)!=k2_tarski(k1_xboole_0,u1_struct_0(X36))|v2_tdlat_3(X36)|~l1_pre_topc(X36))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tdlat_3])])])).
% 0.13/0.38  fof(c_0_66, plain, ![X7, X8]:k1_enumset1(X7,X7,X8)=k2_tarski(X7,X8), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_67, plain, ![X25, X26]:((~v1_tops_2(X26,X25)|r1_tarski(X26,u1_pre_topc(X25))|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))|~l1_pre_topc(X25))&(~r1_tarski(X26,u1_pre_topc(X25))|v1_tops_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))|~l1_pre_topc(X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_tops_2])])])])).
% 0.13/0.38  cnf(c_0_68, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.38  cnf(c_0_69, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (u1_struct_0(esk1_0)=u1_struct_0(esk2_0)|~m1_pre_topc(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_64, c_0_49])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (m1_pre_topc(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_45]), c_0_34])])).
% 0.13/0.38  cnf(c_0_72, plain, (u1_pre_topc(X1)=k2_tarski(k1_xboole_0,u1_struct_0(X1))|~v2_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.38  cnf(c_0_73, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.13/0.38  fof(c_0_74, plain, ![X21, X22, X23, X24]:(~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))|(~m1_pre_topc(X23,X21)|(~v1_tops_2(X22,X21)|(~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|(X24!=X22|v1_tops_2(X24,X23))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_2])])])).
% 0.13/0.38  fof(c_0_75, plain, ![X18, X19, X20]:(~l1_pre_topc(X18)|(~m1_pre_topc(X19,X18)|(~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_2])])])).
% 0.13/0.38  cnf(c_0_76, plain, (r1_tarski(X1,u1_pre_topc(X2))|~v1_tops_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.38  cnf(c_0_77, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.38  cnf(c_0_78, plain, (r1_tarski(u1_pre_topc(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.13/0.38  cnf(c_0_79, negated_conjecture, (u1_struct_0(esk1_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_36]), c_0_71])])).
% 0.13/0.38  cnf(c_0_80, plain, (v2_tdlat_3(X1)|u1_pre_topc(X1)!=k2_tarski(k1_xboole_0,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.38  cnf(c_0_81, plain, (u1_pre_topc(X1)=k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(X1))|~l1_pre_topc(X1)|~v2_tdlat_3(X1)), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 0.13/0.38  cnf(c_0_82, plain, (v1_tops_2(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_pre_topc(X3,X1)|~v1_tops_2(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.13/0.38  cnf(c_0_83, plain, (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.13/0.38  cnf(c_0_84, plain, (v1_tops_2(X1,X2)|~r1_tarski(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.38  cnf(c_0_85, plain, (r1_tarski(X1,u1_pre_topc(X2))|~v1_tops_2(X1,X2)|~l1_pre_topc(X2)|~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.13/0.38  cnf(c_0_86, negated_conjecture, (r1_tarski(u1_pre_topc(esk1_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_27])])).
% 0.13/0.38  cnf(c_0_87, plain, (v2_tdlat_3(X1)|u1_pre_topc(X1)!=k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(rw,[status(thm)],[c_0_80, c_0_73])).
% 0.13/0.38  cnf(c_0_88, negated_conjecture, (k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(esk2_0))=u1_pre_topc(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_79]), c_0_43]), c_0_27])])).
% 0.13/0.38  cnf(c_0_89, negated_conjecture, (~v2_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_90, plain, (v1_tops_2(X1,X2)|~v1_tops_2(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_82]), c_0_83])).
% 0.13/0.38  cnf(c_0_91, plain, (v1_tops_2(X1,X2)|~l1_pre_topc(X2)|~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_84, c_0_77])).
% 0.13/0.38  cnf(c_0_92, negated_conjecture, (r1_tarski(u1_pre_topc(esk1_0),u1_pre_topc(esk2_0))|~v1_tops_2(u1_pre_topc(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_34])])).
% 0.13/0.38  cnf(c_0_93, negated_conjecture, (u1_pre_topc(esk1_0)!=u1_pre_topc(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_34])]), c_0_89])).
% 0.13/0.38  cnf(c_0_94, negated_conjecture, (r1_tarski(X1,u1_pre_topc(esk1_0))|~v1_tops_2(X1,esk1_0)|~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_79]), c_0_27])])).
% 0.13/0.38  cnf(c_0_95, plain, (v1_tops_2(X1,X2)|~v1_tops_2(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_90, c_0_77])).
% 0.13/0.38  cnf(c_0_96, negated_conjecture, (v1_tops_2(X1,esk1_0)|~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,u1_pre_topc(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_79]), c_0_27])])).
% 0.13/0.38  cnf(c_0_97, negated_conjecture, (~v1_tops_2(u1_pre_topc(esk1_0),esk2_0)|~r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk1_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_92]), c_0_93])).
% 0.13/0.38  cnf(c_0_98, negated_conjecture, (r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk1_0))|~v1_tops_2(u1_pre_topc(esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_78]), c_0_34])])).
% 0.13/0.38  cnf(c_0_99, negated_conjecture, (v1_tops_2(u1_pre_topc(esk1_0),esk2_0)|~v1_tops_2(u1_pre_topc(esk1_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_95, c_0_86])).
% 0.13/0.38  cnf(c_0_100, negated_conjecture, (v1_tops_2(u1_pre_topc(esk1_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_86]), c_0_31])])).
% 0.13/0.38  cnf(c_0_101, negated_conjecture, (v1_tops_2(X1,esk1_0)|~v1_tops_2(X1,X2)|~m1_pre_topc(esk1_0,X2)|~l1_pre_topc(X2)|~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_95, c_0_79])).
% 0.13/0.38  cnf(c_0_102, negated_conjecture, (~v1_tops_2(u1_pre_topc(esk1_0),esk2_0)|~v1_tops_2(u1_pre_topc(esk2_0),esk1_0)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.13/0.38  cnf(c_0_103, negated_conjecture, (v1_tops_2(u1_pre_topc(esk1_0),esk2_0)|~m1_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_27])])).
% 0.13/0.38  cnf(c_0_104, negated_conjecture, (v1_tops_2(u1_pre_topc(esk2_0),esk1_0)|~v1_tops_2(u1_pre_topc(esk2_0),X1)|~m1_pre_topc(esk1_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_78]), c_0_34])])).
% 0.13/0.38  cnf(c_0_105, plain, (v1_tops_2(u1_pre_topc(X1),X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_69]), c_0_31])])).
% 0.13/0.38  cnf(c_0_106, negated_conjecture, (~v1_tops_2(u1_pre_topc(esk2_0),esk1_0)|~m1_pre_topc(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.13/0.38  cnf(c_0_107, negated_conjecture, (v1_tops_2(u1_pre_topc(esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_49]), c_0_34])])).
% 0.13/0.38  cnf(c_0_108, negated_conjecture, (~m1_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_107])])).
% 0.13/0.38  cnf(c_0_109, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_36]), c_0_71])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 110
% 0.13/0.38  # Proof object clause steps            : 75
% 0.13/0.38  # Proof object formula steps           : 35
% 0.13/0.38  # Proof object conjectures             : 45
% 0.13/0.38  # Proof object clause conjectures      : 42
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 26
% 0.13/0.38  # Proof object initial formulas used   : 17
% 0.13/0.38  # Proof object generating inferences   : 42
% 0.13/0.38  # Proof object simplifying inferences  : 71
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 17
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 29
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 28
% 0.13/0.38  # Processed clauses                    : 211
% 0.13/0.38  # ...of these trivial                  : 16
% 0.13/0.38  # ...subsumed                          : 37
% 0.13/0.38  # ...remaining for further processing  : 158
% 0.13/0.38  # Other redundant clauses eliminated   : 3
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 3
% 0.13/0.38  # Backward-rewritten                   : 16
% 0.13/0.38  # Generated clauses                    : 356
% 0.13/0.38  # ...of the previous two non-trivial   : 276
% 0.13/0.38  # Contextual simplify-reflections      : 7
% 0.13/0.38  # Paramodulations                      : 353
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 110
% 0.13/0.38  #    Positive orientable unit clauses  : 26
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 81
% 0.13/0.38  # Current number of unprocessed clauses: 115
% 0.13/0.38  # ...number of literals in the above   : 376
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 46
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1563
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 935
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 44
% 0.13/0.38  # Unit Clause-clause subsumption calls : 107
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 27
% 0.13/0.38  # BW rewrite match successes           : 7
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 9297
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.033 s
% 0.13/0.38  # System time              : 0.002 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
