%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:22 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 (5945 expanded)
%              Number of clauses        :   73 (2289 expanded)
%              Number of leaves         :   18 (1461 expanded)
%              Depth                    :   20
%              Number of atoms          :  366 (21666 expanded)
%              Number of equality atoms :   26 (2602 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & v1_tdlat_3(X1) )
           => v1_tdlat_3(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tex_2)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(t58_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_pre_topc)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(t12_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X2 = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
               => ( m1_pre_topc(X2,X1)
                <=> m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

fof(t31_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
             => m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t78_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> r1_tarski(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

fof(d1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
      <=> u1_pre_topc(X1) = k9_setfam_1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & v1_tdlat_3(X1) )
             => v1_tdlat_3(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_tex_2])).

fof(c_0_19,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
      | m1_pre_topc(X14,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

fof(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & l1_pre_topc(esk2_0)
    & g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    & v1_tdlat_3(esk1_0)
    & ~ v1_tdlat_3(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_21,plain,(
    ! [X15,X16] :
      ( ( ~ m1_pre_topc(X15,X16)
        | m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( ~ m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | m1_pre_topc(X15,X16)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_22,plain,(
    ! [X9,X10] :
      ( ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | l1_pre_topc(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_23,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_24,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X32] :
      ( ~ l1_pre_topc(X32)
      | m1_pre_topc(X32,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_30,plain,(
    ! [X39] :
      ( ~ l1_pre_topc(X39)
      | ~ v1_tdlat_3(X39)
      | v2_pre_topc(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

fof(c_0_31,plain,(
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

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_34,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_36,plain,(
    ! [X7,X8] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X8,X7)
      | v2_pre_topc(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_37,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v1_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

fof(c_0_43,plain,(
    ! [X27,X28] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)))
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)),X27)
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

fof(c_0_44,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))
      | v2_pre_topc(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_pre_topc])])).

cnf(c_0_45,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk1_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_26])])).

cnf(c_0_48,plain,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_42]),c_0_26])])).

cnf(c_0_50,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_26])])).

fof(c_0_52,plain,(
    ! [X36,X37,X38] :
      ( ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_pre_topc(X37,X36)
      | ~ m1_pre_topc(X38,X37)
      | m1_pre_topc(X38,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_53,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_26]),c_0_47])])).

cnf(c_0_55,negated_conjecture,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_42]),c_0_26]),c_0_47])])).

cnf(c_0_56,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_35])])).

cnf(c_0_57,negated_conjecture,
    ( m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_51]),c_0_35])])).

cnf(c_0_58,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_59,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_35])])).

cnf(c_0_61,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_37]),c_0_35])])).

fof(c_0_62,plain,(
    ! [X29,X30,X31] :
      ( ( ~ m1_pre_topc(X30,X29)
        | m1_pre_topc(X31,X29)
        | X30 != g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31))
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ l1_pre_topc(X29) )
      & ( ~ m1_pre_topc(X31,X29)
        | m1_pre_topc(X30,X29)
        | X30 != g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31))
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).

cnf(c_0_63,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ m1_pre_topc(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_25])).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_37]),c_0_26])])).

cnf(c_0_65,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_56]),c_0_61])])).

cnf(c_0_67,plain,
    ( m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | X1 != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])])).

cnf(c_0_69,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_61]),c_0_35]),c_0_66])])).

cnf(c_0_71,plain,
    ( m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_67,c_0_28])]),c_0_53])).

cnf(c_0_72,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_68])])).

cnf(c_0_73,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_68])])).

fof(c_0_74,plain,(
    ! [X20,X21,X22,X23] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
      | ~ m1_pre_topc(X22,X20)
      | ~ v1_tops_2(X21,X20)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
      | X23 != X21
      | v1_tops_2(X23,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_2])])])).

fof(c_0_75,plain,(
    ! [X17,X18,X19] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))
      | m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_2])])])).

fof(c_0_76,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(X11)
      | m1_subset_1(u1_pre_topc(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ r1_tarski(u1_struct_0(esk2_0),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_64]),c_0_35]),c_0_66])])).

cnf(c_0_79,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_35]),c_0_26]),c_0_73])])).

fof(c_0_80,plain,(
    ! [X24,X25] :
      ( ( ~ v1_tops_2(X25,X24)
        | r1_tarski(X25,u1_pre_topc(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))
        | ~ l1_pre_topc(X24) )
      & ( ~ r1_tarski(X25,u1_pre_topc(X24))
        | v1_tops_2(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_tops_2])])])])).

cnf(c_0_81,plain,
    ( v1_tops_2(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_82,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_64]),c_0_79])])).

cnf(c_0_85,plain,
    ( v1_tops_2(X1,X2)
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_86,plain,
    ( v1_tops_2(X1,X2)
    | ~ v1_tops_2(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_81]),c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_26])])).

cnf(c_0_88,negated_conjecture,
    ( v1_tops_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ r1_tarski(X1,u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_84]),c_0_26])])).

fof(c_0_89,plain,(
    ! [X40] :
      ( ( ~ v1_tdlat_3(X40)
        | u1_pre_topc(X40) = k9_setfam_1(u1_struct_0(X40))
        | ~ l1_pre_topc(X40) )
      & ( u1_pre_topc(X40) != k9_setfam_1(u1_struct_0(X40))
        | v1_tdlat_3(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tdlat_3])])])).

cnf(c_0_90,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk1_0),esk2_0)
    | ~ v1_tops_2(u1_pre_topc(esk1_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_87]),c_0_41])])).

cnf(c_0_92,plain,
    ( u1_pre_topc(X1) = k9_setfam_1(u1_struct_0(X1))
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_93,plain,
    ( r1_tarski(X1,u1_pre_topc(X2))
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_94,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_79]),c_0_26])])).

cnf(c_0_95,plain,
    ( v1_tdlat_3(X1)
    | u1_pre_topc(X1) != k9_setfam_1(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( k9_setfam_1(u1_struct_0(esk2_0)) = u1_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_84]),c_0_39]),c_0_26])])).

cnf(c_0_97,negated_conjecture,
    ( ~ v1_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk1_0),u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_87]),c_0_35])]),c_0_94])])).

cnf(c_0_99,negated_conjecture,
    ( u1_pre_topc(esk1_0) != u1_pre_topc(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_35])]),c_0_97])).

cnf(c_0_100,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_28])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(X1,u1_pre_topc(esk1_0))
    | ~ v1_tops_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_84]),c_0_26])])).

cnf(c_0_102,negated_conjecture,
    ( ~ r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_98]),c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_84]),c_0_26])])).

cnf(c_0_104,negated_conjecture,
    ( v1_tops_2(X1,esk1_0)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk1_0,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_84])).

cnf(c_0_105,negated_conjecture,
    ( ~ v1_tops_2(u1_pre_topc(esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_83]),c_0_35])]),c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(X1),esk2_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ r1_tarski(u1_pre_topc(X1),u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_103]),c_0_35])])).

cnf(c_0_107,negated_conjecture,
    ( ~ v1_tops_2(u1_pre_topc(esk2_0),X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_83]),c_0_35])]),c_0_105])).

cnf(c_0_108,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_41]),c_0_79])])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_64]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.44  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.029 s
% 0.20/0.44  # Presaturation interreduction done
% 0.20/0.44  
% 0.20/0.44  # Proof found!
% 0.20/0.44  # SZS status Theorem
% 0.20/0.44  # SZS output start CNFRefutation
% 0.20/0.44  fof(t17_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v1_tdlat_3(X1))=>v1_tdlat_3(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tex_2)).
% 0.20/0.44  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.20/0.44  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.20/0.44  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.44  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.20/0.44  fof(cc1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 0.20/0.44  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.20/0.44  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.20/0.44  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 0.20/0.44  fof(t58_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_pre_topc)).
% 0.20/0.44  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.20/0.44  fof(t12_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X2=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=>(m1_pre_topc(X2,X1)<=>m1_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 0.20/0.44  fof(t35_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_pre_topc(X3,X1)=>(v1_tops_2(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))=>(X4=X2=>v1_tops_2(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_2)).
% 0.20/0.44  fof(t31_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))=>m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_2)).
% 0.20/0.44  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.20/0.44  fof(t78_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>r1_tarski(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 0.20/0.44  fof(d1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)<=>u1_pre_topc(X1)=k9_setfam_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tdlat_3)).
% 0.20/0.44  fof(c_0_18, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v1_tdlat_3(X1))=>v1_tdlat_3(X2))))), inference(assume_negation,[status(cth)],[t17_tex_2])).
% 0.20/0.44  fof(c_0_19, plain, ![X13, X14]:(~l1_pre_topc(X13)|(~m1_pre_topc(X14,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))|m1_pre_topc(X14,X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.20/0.44  fof(c_0_20, negated_conjecture, (l1_pre_topc(esk1_0)&(l1_pre_topc(esk2_0)&((g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))&v1_tdlat_3(esk1_0))&~v1_tdlat_3(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.20/0.44  fof(c_0_21, plain, ![X15, X16]:((~m1_pre_topc(X15,X16)|m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))|~l1_pre_topc(X16)|~l1_pre_topc(X15))&(~m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))|m1_pre_topc(X15,X16)|~l1_pre_topc(X16)|~l1_pre_topc(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.20/0.44  fof(c_0_22, plain, ![X9, X10]:(~l1_pre_topc(X9)|(~m1_pre_topc(X10,X9)|l1_pre_topc(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.44  fof(c_0_23, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.44  cnf(c_0_24, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.44  cnf(c_0_25, negated_conjecture, (g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.44  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.44  cnf(c_0_27, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.44  cnf(c_0_28, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.44  fof(c_0_29, plain, ![X32]:(~l1_pre_topc(X32)|m1_pre_topc(X32,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.20/0.44  fof(c_0_30, plain, ![X39]:(~l1_pre_topc(X39)|(~v1_tdlat_3(X39)|v2_pre_topc(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).
% 0.20/0.44  fof(c_0_31, plain, ![X33, X34, X35]:((~r1_tarski(u1_struct_0(X34),u1_struct_0(X35))|m1_pre_topc(X34,X35)|~m1_pre_topc(X35,X33)|~m1_pre_topc(X34,X33)|(~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(~m1_pre_topc(X34,X35)|r1_tarski(u1_struct_0(X34),u1_struct_0(X35))|~m1_pre_topc(X35,X33)|~m1_pre_topc(X34,X33)|(~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.20/0.44  cnf(c_0_32, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  cnf(c_0_33, negated_conjecture, (m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.20/0.44  cnf(c_0_34, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.44  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.44  fof(c_0_36, plain, ![X7, X8]:(~v2_pre_topc(X7)|~l1_pre_topc(X7)|(~m1_pre_topc(X8,X7)|v2_pre_topc(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.20/0.44  cnf(c_0_37, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.44  cnf(c_0_38, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.44  cnf(c_0_39, negated_conjecture, (v1_tdlat_3(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.44  cnf(c_0_40, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.44  cnf(c_0_41, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_32])).
% 0.20/0.44  cnf(c_0_42, negated_conjecture, (m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.20/0.44  fof(c_0_43, plain, ![X27, X28]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)))|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)),X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 0.20/0.44  fof(c_0_44, plain, ![X12]:(~l1_pre_topc(X12)|(~v2_pre_topc(g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_pre_topc])])).
% 0.20/0.44  cnf(c_0_45, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.44  cnf(c_0_46, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk1_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(spm,[status(thm)],[c_0_33, c_0_37])).
% 0.20/0.44  cnf(c_0_47, negated_conjecture, (v2_pre_topc(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_26])])).
% 0.20/0.44  cnf(c_0_48, plain, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.44  cnf(c_0_49, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_42]), c_0_26])])).
% 0.20/0.44  cnf(c_0_50, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.44  cnf(c_0_51, negated_conjecture, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_25]), c_0_26])])).
% 0.20/0.44  fof(c_0_52, plain, ![X36, X37, X38]:(~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~m1_pre_topc(X37,X36)|(~m1_pre_topc(X38,X37)|m1_pre_topc(X38,X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.20/0.44  cnf(c_0_53, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.44  cnf(c_0_54, negated_conjecture, (v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_26]), c_0_47])])).
% 0.20/0.44  cnf(c_0_55, negated_conjecture, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_42]), c_0_26]), c_0_47])])).
% 0.20/0.44  cnf(c_0_56, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_35])])).
% 0.20/0.44  cnf(c_0_57, negated_conjecture, (m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_51]), c_0_35])])).
% 0.20/0.44  cnf(c_0_58, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.44  cnf(c_0_59, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.44  cnf(c_0_60, negated_conjecture, (v2_pre_topc(esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_35])])).
% 0.20/0.44  cnf(c_0_61, negated_conjecture, (m1_pre_topc(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_37]), c_0_35])])).
% 0.20/0.44  fof(c_0_62, plain, ![X29, X30, X31]:((~m1_pre_topc(X30,X29)|m1_pre_topc(X31,X29)|X30!=g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31))|(~v2_pre_topc(X31)|~l1_pre_topc(X31))|(~v2_pre_topc(X30)|~l1_pre_topc(X30))|~l1_pre_topc(X29))&(~m1_pre_topc(X31,X29)|m1_pre_topc(X30,X29)|X30!=g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31))|(~v2_pre_topc(X31)|~l1_pre_topc(X31))|(~v2_pre_topc(X30)|~l1_pre_topc(X30))|~l1_pre_topc(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).
% 0.20/0.44  cnf(c_0_63, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~m1_pre_topc(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_56, c_0_25])).
% 0.20/0.44  cnf(c_0_64, negated_conjecture, (m1_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_37]), c_0_26])])).
% 0.20/0.44  cnf(c_0_65, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X3)|~v2_pre_topc(X3)), inference(csr,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.44  cnf(c_0_66, negated_conjecture, (v2_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_56]), c_0_61])])).
% 0.20/0.44  cnf(c_0_67, plain, (m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|X1!=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.44  cnf(c_0_68, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64])])).
% 0.20/0.44  cnf(c_0_69, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  cnf(c_0_70, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_61]), c_0_35]), c_0_66])])).
% 0.20/0.44  cnf(c_0_71, plain, (m1_pre_topc(X1,X2)|~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_67, c_0_28])]), c_0_53])).
% 0.20/0.44  cnf(c_0_72, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_68])])).
% 0.20/0.44  cnf(c_0_73, negated_conjecture, (v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_68])])).
% 0.20/0.44  fof(c_0_74, plain, ![X20, X21, X22, X23]:(~l1_pre_topc(X20)|(~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|(~m1_pre_topc(X22,X20)|(~v1_tops_2(X21,X20)|(~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|(X23!=X21|v1_tops_2(X23,X22))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_2])])])).
% 0.20/0.44  fof(c_0_75, plain, ![X17, X18, X19]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,X17)|(~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))|m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_2])])])).
% 0.20/0.44  fof(c_0_76, plain, ![X11]:(~l1_pre_topc(X11)|m1_subset_1(u1_pre_topc(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.20/0.44  cnf(c_0_77, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(X1)|~m1_pre_topc(X1,esk2_0)|~r1_tarski(u1_struct_0(esk2_0),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.44  cnf(c_0_78, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0))|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_64]), c_0_35]), c_0_66])])).
% 0.20/0.44  cnf(c_0_79, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_35]), c_0_26]), c_0_73])])).
% 0.20/0.44  fof(c_0_80, plain, ![X24, X25]:((~v1_tops_2(X25,X24)|r1_tarski(X25,u1_pre_topc(X24))|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|~l1_pre_topc(X24))&(~r1_tarski(X25,u1_pre_topc(X24))|v1_tops_2(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|~l1_pre_topc(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_tops_2])])])])).
% 0.20/0.44  cnf(c_0_81, plain, (v1_tops_2(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_pre_topc(X3,X1)|~v1_tops_2(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.44  cnf(c_0_82, plain, (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.44  cnf(c_0_83, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.44  cnf(c_0_84, negated_conjecture, (u1_struct_0(esk1_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_64]), c_0_79])])).
% 0.20/0.44  cnf(c_0_85, plain, (v1_tops_2(X1,X2)|~r1_tarski(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.44  cnf(c_0_86, plain, (v1_tops_2(X1,X2)|~v1_tops_2(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_81]), c_0_82])).
% 0.20/0.44  cnf(c_0_87, negated_conjecture, (m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_26])])).
% 0.20/0.44  cnf(c_0_88, negated_conjecture, (v1_tops_2(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~r1_tarski(X1,u1_pre_topc(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_84]), c_0_26])])).
% 0.20/0.44  fof(c_0_89, plain, ![X40]:((~v1_tdlat_3(X40)|u1_pre_topc(X40)=k9_setfam_1(u1_struct_0(X40))|~l1_pre_topc(X40))&(u1_pre_topc(X40)!=k9_setfam_1(u1_struct_0(X40))|v1_tdlat_3(X40)|~l1_pre_topc(X40))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tdlat_3])])])).
% 0.20/0.44  cnf(c_0_90, negated_conjecture, (v1_tops_2(u1_pre_topc(esk1_0),esk2_0)|~v1_tops_2(u1_pre_topc(esk1_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.44  cnf(c_0_91, negated_conjecture, (v1_tops_2(u1_pre_topc(esk1_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_87]), c_0_41])])).
% 0.20/0.44  cnf(c_0_92, plain, (u1_pre_topc(X1)=k9_setfam_1(u1_struct_0(X1))|~v1_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.44  cnf(c_0_93, plain, (r1_tarski(X1,u1_pre_topc(X2))|~v1_tops_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.44  cnf(c_0_94, negated_conjecture, (v1_tops_2(u1_pre_topc(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_79]), c_0_26])])).
% 0.20/0.44  cnf(c_0_95, plain, (v1_tdlat_3(X1)|u1_pre_topc(X1)!=k9_setfam_1(u1_struct_0(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.44  cnf(c_0_96, negated_conjecture, (k9_setfam_1(u1_struct_0(esk2_0))=u1_pre_topc(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_84]), c_0_39]), c_0_26])])).
% 0.20/0.44  cnf(c_0_97, negated_conjecture, (~v1_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.44  cnf(c_0_98, negated_conjecture, (r1_tarski(u1_pre_topc(esk1_0),u1_pre_topc(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_87]), c_0_35])]), c_0_94])])).
% 0.20/0.44  cnf(c_0_99, negated_conjecture, (u1_pre_topc(esk1_0)!=u1_pre_topc(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_35])]), c_0_97])).
% 0.20/0.44  cnf(c_0_100, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_28])).
% 0.20/0.44  cnf(c_0_101, negated_conjecture, (r1_tarski(X1,u1_pre_topc(esk1_0))|~v1_tops_2(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_84]), c_0_26])])).
% 0.20/0.44  cnf(c_0_102, negated_conjecture, (~r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk1_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_98]), c_0_99])).
% 0.20/0.44  cnf(c_0_103, negated_conjecture, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_84]), c_0_26])])).
% 0.20/0.44  cnf(c_0_104, negated_conjecture, (v1_tops_2(X1,esk1_0)|~v1_tops_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~m1_pre_topc(esk1_0,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_86, c_0_84])).
% 0.20/0.44  cnf(c_0_105, negated_conjecture, (~v1_tops_2(u1_pre_topc(esk2_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_83]), c_0_35])]), c_0_102])).
% 0.20/0.44  cnf(c_0_106, negated_conjecture, (v1_tops_2(u1_pre_topc(X1),esk2_0)|~m1_pre_topc(X1,esk1_0)|~r1_tarski(u1_pre_topc(X1),u1_pre_topc(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_103]), c_0_35])])).
% 0.20/0.44  cnf(c_0_107, negated_conjecture, (~v1_tops_2(u1_pre_topc(esk2_0),X1)|~m1_pre_topc(esk1_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_83]), c_0_35])]), c_0_105])).
% 0.20/0.44  cnf(c_0_108, negated_conjecture, (v1_tops_2(u1_pre_topc(esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_41]), c_0_79])])).
% 0.20/0.44  cnf(c_0_109, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_64]), c_0_35])]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 110
% 0.20/0.44  # Proof object clause steps            : 73
% 0.20/0.44  # Proof object formula steps           : 37
% 0.20/0.44  # Proof object conjectures             : 48
% 0.20/0.44  # Proof object clause conjectures      : 45
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 26
% 0.20/0.44  # Proof object initial formulas used   : 18
% 0.20/0.44  # Proof object generating inferences   : 39
% 0.20/0.44  # Proof object simplifying inferences  : 93
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 19
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 31
% 0.20/0.44  # Removed in clause preprocessing      : 0
% 0.20/0.44  # Initial clauses in saturation        : 31
% 0.20/0.44  # Processed clauses                    : 943
% 0.20/0.44  # ...of these trivial                  : 70
% 0.20/0.44  # ...subsumed                          : 536
% 0.20/0.44  # ...remaining for further processing  : 337
% 0.20/0.44  # Other redundant clauses eliminated   : 5
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 7
% 0.20/0.44  # Backward-rewritten                   : 26
% 0.20/0.44  # Generated clauses                    : 3229
% 0.20/0.44  # ...of the previous two non-trivial   : 2056
% 0.20/0.44  # Contextual simplify-reflections      : 47
% 0.20/0.44  # Paramodulations                      : 3224
% 0.20/0.44  # Factorizations                       : 0
% 0.20/0.44  # Equation resolutions                 : 5
% 0.20/0.44  # Propositional unsat checks           : 0
% 0.20/0.44  #    Propositional check models        : 0
% 0.20/0.44  #    Propositional check unsatisfiable : 0
% 0.20/0.44  #    Propositional clauses             : 0
% 0.20/0.44  #    Propositional clauses after purity: 0
% 0.20/0.44  #    Propositional unsat core size     : 0
% 0.20/0.44  #    Propositional preprocessing time  : 0.000
% 0.20/0.44  #    Propositional encoding time       : 0.000
% 0.20/0.44  #    Propositional solver time         : 0.000
% 0.20/0.44  #    Success case prop preproc time    : 0.000
% 0.20/0.44  #    Success case prop encoding time   : 0.000
% 0.20/0.44  #    Success case prop solver time     : 0.000
% 0.20/0.44  # Current number of processed clauses  : 271
% 0.20/0.44  #    Positive orientable unit clauses  : 68
% 0.20/0.44  #    Positive unorientable unit clauses: 0
% 0.20/0.44  #    Negative unit clauses             : 4
% 0.20/0.44  #    Non-unit-clauses                  : 199
% 0.20/0.44  # Current number of unprocessed clauses: 1134
% 0.20/0.44  # ...number of literals in the above   : 3544
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 61
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 11179
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 6397
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 587
% 0.20/0.44  # Unit Clause-clause subsumption calls : 138
% 0.20/0.44  # Rewrite failures with RHS unbound    : 0
% 0.20/0.44  # BW rewrite match attempts            : 213
% 0.20/0.44  # BW rewrite match successes           : 14
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 96949
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.097 s
% 0.20/0.44  # System time              : 0.003 s
% 0.20/0.44  # Total time               : 0.100 s
% 0.20/0.44  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
