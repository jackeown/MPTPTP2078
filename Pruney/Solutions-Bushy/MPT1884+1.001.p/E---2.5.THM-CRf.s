%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1884+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:58 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  195 (921193 expanded)
%              Number of clauses        :  162 (335793 expanded)
%              Number of leaves         :   16 (225339 expanded)
%              Depth                    :   48
%              Number of atoms          :  725 (9133544 expanded)
%              Number of equality atoms :  108 (700409 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

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

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

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
    ! [X39,X40,X41] :
      ( ( ~ v3_tex_2(X41,X39)
        | v4_tex_2(X40,X39)
        | X41 != u1_struct_0(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ m1_pre_topc(X40,X39)
        | v2_struct_0(X39)
        | ~ l1_pre_topc(X39) )
      & ( ~ v4_tex_2(X40,X39)
        | v3_tex_2(X41,X39)
        | X41 != u1_struct_0(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ m1_pre_topc(X40,X39)
        | v2_struct_0(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t51_tex_2])])])])])).

fof(c_0_18,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_pre_topc(X27,X26)
      | m1_subset_1(u1_struct_0(X27),k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_19,negated_conjecture,(
    ! [X50] :
      ( ~ v2_struct_0(esk6_0)
      & v2_pre_topc(esk6_0)
      & l1_pre_topc(esk6_0)
      & ~ v2_struct_0(esk7_0)
      & m1_pre_topc(esk7_0,esk6_0)
      & ( ~ v2_struct_0(esk8_0)
        | ~ v1_tdlat_3(esk7_0)
        | ~ v4_tex_2(esk7_0,esk6_0) )
      & ( v1_tdlat_3(esk8_0)
        | ~ v1_tdlat_3(esk7_0)
        | ~ v4_tex_2(esk7_0,esk6_0) )
      & ( m1_pre_topc(esk8_0,esk6_0)
        | ~ v1_tdlat_3(esk7_0)
        | ~ v4_tex_2(esk7_0,esk6_0) )
      & ( m1_pre_topc(esk7_0,esk8_0)
        | ~ v1_tdlat_3(esk7_0)
        | ~ v4_tex_2(esk7_0,esk6_0) )
      & ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) != g1_pre_topc(u1_struct_0(esk8_0),u1_pre_topc(esk8_0))
        | ~ v1_tdlat_3(esk7_0)
        | ~ v4_tex_2(esk7_0,esk6_0) )
      & ( v1_tdlat_3(esk7_0)
        | v4_tex_2(esk7_0,esk6_0) )
      & ( v2_struct_0(X50)
        | ~ v1_tdlat_3(X50)
        | ~ m1_pre_topc(X50,esk6_0)
        | ~ m1_pre_topc(esk7_0,X50)
        | g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) = g1_pre_topc(u1_struct_0(X50),u1_pre_topc(X50))
        | v4_tex_2(esk7_0,esk6_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).

cnf(c_0_20,plain,
    ( v3_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ v4_tex_2(X1,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X14,X15] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X14)
      | l1_pre_topc(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_23,plain,(
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

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | v3_tex_2(u1_struct_0(X2),X1)
    | ~ v4_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X16] :
      ( ~ l1_pre_topc(X16)
      | m1_subset_1(u1_pre_topc(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_29,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X28,X29,X30] :
      ( ( ~ v2_tex_2(X30,X28)
        | v1_tdlat_3(X29)
        | X30 != u1_struct_0(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ v1_tdlat_3(X29)
        | v2_tex_2(X30,X28)
        | X30 != u1_struct_0(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

cnf(c_0_31,plain,
    ( v2_tex_2(X1,X2)
    | ~ v3_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_24]),c_0_25])])).

cnf(c_0_33,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk7_0),esk6_0)
    | ~ v4_tex_2(esk7_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_24]),c_0_25])]),c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( v1_tdlat_3(esk7_0)
    | v4_tex_2(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_35,plain,(
    ! [X12,X13] :
      ( ( v1_pre_topc(g1_pre_topc(X12,X13))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))) )
      & ( l1_pre_topc(g1_pre_topc(X12,X13))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_36,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_24]),c_0_25])])).

cnf(c_0_38,plain,
    ( v1_tdlat_3(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | X1 != u1_struct_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v2_tex_2(u1_struct_0(esk7_0),esk6_0)
    | ~ v3_tex_2(u1_struct_0(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_25])])).

cnf(c_0_40,negated_conjecture,
    ( v1_tdlat_3(esk7_0)
    | v3_tex_2(u1_struct_0(esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_41,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_42,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( v2_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_tex_2(u1_struct_0(X1),X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( v1_tdlat_3(esk7_0)
    | v2_tex_2(u1_struct_0(esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_49,plain,(
    ! [X22,X23,X24,X25] :
      ( ( X22 = X24
        | g1_pre_topc(X22,X23) != g1_pre_topc(X24,X25)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22))) )
      & ( X23 = X25
        | g1_pre_topc(X22,X23) != g1_pre_topc(X24,X25)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

cnf(c_0_50,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_tex_2(u1_struct_0(X2),X1)
    | ~ v1_tdlat_3(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]),c_0_21])).

cnf(c_0_54,negated_conjecture,
    ( v1_tdlat_3(esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_24]),c_0_25])]),c_0_27]),c_0_47]),c_0_48])).

cnf(c_0_55,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))),u1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))) = g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

fof(c_0_57,plain,(
    ! [X31,X32] :
      ( ( ~ v2_struct_0(esk5_2(X31,X32))
        | ~ v2_tex_2(X32,X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( v1_pre_topc(esk5_2(X31,X32))
        | ~ v2_tex_2(X32,X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( v1_tdlat_3(esk5_2(X31,X32))
        | ~ v2_tex_2(X32,X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_pre_topc(esk5_2(X31,X32),X31)
        | ~ v2_tex_2(X32,X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( X32 = u1_struct_0(esk5_2(X31,X32))
        | ~ v2_tex_2(X32,X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).

cnf(c_0_58,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_59,negated_conjecture,
    ( v2_tex_2(u1_struct_0(esk7_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_24]),c_0_54]),c_0_25])]),c_0_47]),c_0_27])).

cnf(c_0_60,plain,
    ( v2_tex_2(esk1_2(X1,X2),X1)
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_61,negated_conjecture,
    ( X1 = u1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | g1_pre_topc(X2,X1) != g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_62,plain,(
    ! [X36,X37,X38] :
      ( ( ~ r1_tarski(u1_struct_0(X37),u1_struct_0(X38))
        | m1_pre_topc(X37,X38)
        | ~ m1_pre_topc(X38,X36)
        | ~ m1_pre_topc(X37,X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( ~ m1_pre_topc(X37,X38)
        | r1_tarski(u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_pre_topc(X38,X36)
        | ~ m1_pre_topc(X37,X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_63,plain,
    ( m1_pre_topc(esk5_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk7_0),esk6_0)
    | m1_subset_1(esk1_2(esk6_0,u1_struct_0(esk7_0)),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_32]),c_0_25])]),c_0_59])])).

cnf(c_0_65,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_66,negated_conjecture,
    ( v2_tex_2(esk1_2(esk6_0,u1_struct_0(esk7_0)),esk6_0)
    | v3_tex_2(u1_struct_0(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_32]),c_0_25])]),c_0_59])])).

cnf(c_0_67,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) = u1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_61]),c_0_43])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_51])).

cnf(c_0_69,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( m1_pre_topc(esk5_2(esk6_0,esk1_2(esk6_0,u1_struct_0(esk7_0))),esk6_0)
    | v3_tex_2(u1_struct_0(esk7_0),esk6_0)
    | v1_xboole_0(esk1_2(esk6_0,u1_struct_0(esk7_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_25])]),c_0_27]),c_0_66])).

cnf(c_0_71,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_72,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))),u1_pre_topc(esk7_0)) = g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( m1_pre_topc(X1,esk5_2(esk6_0,esk1_2(esk6_0,u1_struct_0(esk7_0))))
    | v3_tex_2(u1_struct_0(esk7_0),esk6_0)
    | v1_xboole_0(esk1_2(esk6_0,u1_struct_0(esk7_0)))
    | ~ m1_pre_topc(X1,esk6_0)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(esk5_2(esk6_0,esk1_2(esk6_0,u1_struct_0(esk7_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_65]),c_0_25])])).

cnf(c_0_75,plain,
    ( X1 = u1_struct_0(esk5_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,esk1_2(X2,X1))
    | v3_tex_2(X1,X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_77,plain,
    ( v4_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ v3_tex_2(X1,X2)
    | X1 != u1_struct_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) = X1
    | g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) != g1_pre_topc(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_79,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk5_2(esk6_0,esk1_2(esk6_0,u1_struct_0(esk7_0))))
    | v3_tex_2(u1_struct_0(esk7_0),esk6_0)
    | v1_xboole_0(esk1_2(esk6_0,u1_struct_0(esk7_0)))
    | ~ r1_tarski(u1_struct_0(esk7_0),u1_struct_0(esk5_2(esk6_0,esk1_2(esk6_0,u1_struct_0(esk7_0))))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_24])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(esk5_2(esk6_0,esk1_2(esk6_0,u1_struct_0(esk7_0)))) = esk1_2(esk6_0,u1_struct_0(esk7_0))
    | v3_tex_2(u1_struct_0(esk7_0),esk6_0)
    | v1_xboole_0(esk1_2(esk6_0,u1_struct_0(esk7_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_64]),c_0_65]),c_0_25])]),c_0_27]),c_0_66])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk7_0),esk1_2(esk6_0,u1_struct_0(esk7_0)))
    | v3_tex_2(u1_struct_0(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_32]),c_0_25])]),c_0_59])])).

cnf(c_0_82,plain,
    ( v1_tdlat_3(esk5_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_83,plain,
    ( v4_tex_2(X1,X2)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v3_tex_2(u1_struct_0(X1),X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_77]),c_0_21])).

cnf(c_0_84,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) = u1_struct_0(esk7_0) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | v4_tex_2(esk7_0,esk6_0)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,esk6_0)
    | ~ m1_pre_topc(esk7_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_86,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk5_2(esk6_0,esk1_2(esk6_0,u1_struct_0(esk7_0))))
    | v3_tex_2(u1_struct_0(esk7_0),esk6_0)
    | v1_xboole_0(esk1_2(esk6_0,u1_struct_0(esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( v1_tdlat_3(esk5_2(esk6_0,esk1_2(esk6_0,u1_struct_0(esk7_0))))
    | v3_tex_2(u1_struct_0(esk7_0),esk6_0)
    | v1_xboole_0(esk1_2(esk6_0,u1_struct_0(esk7_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_64]),c_0_65]),c_0_25])]),c_0_27]),c_0_66])).

cnf(c_0_88,negated_conjecture,
    ( v4_tex_2(esk7_0,esk6_0)
    | ~ v3_tex_2(u1_struct_0(esk7_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_24]),c_0_25])]),c_0_27])).

fof(c_0_89,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X34,k1_zfmisc_1(X35))
        | r1_tarski(X34,X35) )
      & ( ~ r1_tarski(X34,X35)
        | m1_subset_1(X34,k1_zfmisc_1(X35)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_90,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk5_2(X1,X2))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_91,negated_conjecture,
    ( u1_struct_0(esk7_0) = X1
    | g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) != g1_pre_topc(X1,X2) ),
    inference(rw,[status(thm)],[c_0_78,c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk5_2(esk6_0,esk1_2(esk6_0,u1_struct_0(esk7_0)))),u1_pre_topc(esk5_2(esk6_0,esk1_2(esk6_0,u1_struct_0(esk7_0))))) = g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))
    | v4_tex_2(esk7_0,esk6_0)
    | v2_struct_0(esk5_2(esk6_0,esk1_2(esk6_0,u1_struct_0(esk7_0))))
    | v1_xboole_0(esk1_2(esk6_0,u1_struct_0(esk7_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_70]),c_0_86]),c_0_87]),c_0_88])).

fof(c_0_93,plain,(
    ! [X6,X7] :
      ( ~ v1_xboole_0(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_94,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk7_0),esk6_0)
    | v1_xboole_0(esk1_2(esk6_0,u1_struct_0(esk7_0)))
    | ~ v2_struct_0(esk5_2(esk6_0,esk1_2(esk6_0,u1_struct_0(esk7_0)))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_64]),c_0_65]),c_0_25])]),c_0_27]),c_0_66])).

cnf(c_0_96,negated_conjecture,
    ( u1_struct_0(esk5_2(esk6_0,esk1_2(esk6_0,u1_struct_0(esk7_0)))) = u1_struct_0(esk7_0)
    | v4_tex_2(esk7_0,esk6_0)
    | v2_struct_0(esk5_2(esk6_0,esk1_2(esk6_0,u1_struct_0(esk7_0))))
    | v1_xboole_0(esk1_2(esk6_0,u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_97,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk7_0),esk6_0)
    | m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(esk1_2(esk6_0,u1_struct_0(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_81])).

cnf(c_0_99,negated_conjecture,
    ( u1_struct_0(esk5_2(esk6_0,esk1_2(esk6_0,u1_struct_0(esk7_0)))) = u1_struct_0(esk7_0)
    | v4_tex_2(esk7_0,esk6_0)
    | v1_xboole_0(esk1_2(esk6_0,u1_struct_0(esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_88])).

cnf(c_0_100,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk7_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk7_0))
    | ~ v1_xboole_0(esk1_2(esk6_0,u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_101,negated_conjecture,
    ( esk1_2(esk6_0,u1_struct_0(esk7_0)) = u1_struct_0(esk7_0)
    | v4_tex_2(esk7_0,esk6_0)
    | v1_xboole_0(esk1_2(esk6_0,u1_struct_0(esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_99]),c_0_88])).

cnf(c_0_102,negated_conjecture,
    ( m1_pre_topc(esk8_0,esk6_0)
    | ~ v1_tdlat_3(esk7_0)
    | ~ v4_tex_2(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_103,plain,
    ( v3_tex_2(X1,X2)
    | X1 != esk1_2(X2,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_104,negated_conjecture,
    ( esk1_2(esk6_0,u1_struct_0(esk7_0)) = u1_struct_0(esk7_0)
    | v4_tex_2(esk7_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_88])).

fof(c_0_105,plain,(
    ! [X45,X46] :
      ( ~ v1_xboole_0(X45)
      | X45 = X46
      | ~ v1_xboole_0(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_106,negated_conjecture,
    ( m1_pre_topc(esk8_0,esk6_0)
    | ~ v4_tex_2(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_54])])).

cnf(c_0_107,negated_conjecture,
    ( v4_tex_2(esk7_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_59]),c_0_32]),c_0_25])]),c_0_88])).

cnf(c_0_108,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( m1_pre_topc(esk8_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_110,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk8_0)
    | ~ v1_tdlat_3(esk7_0)
    | ~ v4_tex_2(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_111,negated_conjecture,
    ( X1 = u1_struct_0(esk7_0)
    | m1_pre_topc(esk8_0,esk6_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_112,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk8_0)
    | ~ v4_tex_2(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_54])])).

cnf(c_0_113,negated_conjecture,
    ( v1_tdlat_3(esk8_0)
    | ~ v1_tdlat_3(esk7_0)
    | ~ v4_tex_2(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_114,negated_conjecture,
    ( esk1_2(esk6_0,u1_struct_0(esk7_0)) = u1_struct_0(esk7_0)
    | m1_pre_topc(esk8_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_101]),c_0_106])).

cnf(c_0_115,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk8_0)
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_107])).

cnf(c_0_116,negated_conjecture,
    ( v1_tdlat_3(esk8_0)
    | ~ v4_tex_2(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_54])])).

cnf(c_0_117,negated_conjecture,
    ( m1_pre_topc(esk8_0,esk6_0)
    | v3_tex_2(u1_struct_0(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_114]),c_0_59]),c_0_32]),c_0_25])])).

cnf(c_0_118,negated_conjecture,
    ( X1 = u1_struct_0(esk7_0)
    | m1_pre_topc(esk7_0,esk8_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( v1_tdlat_3(esk8_0)
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_107])).

cnf(c_0_120,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_121,negated_conjecture,
    ( m1_pre_topc(esk8_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_117]),c_0_106])).

cnf(c_0_122,negated_conjecture,
    ( esk1_2(esk6_0,u1_struct_0(esk7_0)) = u1_struct_0(esk7_0)
    | m1_pre_topc(esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_101]),c_0_112])).

cnf(c_0_123,negated_conjecture,
    ( X1 = u1_struct_0(esk7_0)
    | v1_tdlat_3(esk8_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_119])).

cnf(c_0_124,plain,
    ( X3 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tex_2(X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ v3_tex_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk8_0))
    | ~ m1_pre_topc(X1,esk6_0)
    | ~ m1_pre_topc(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_65]),c_0_25])])).

cnf(c_0_126,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk8_0)
    | v3_tex_2(u1_struct_0(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_122]),c_0_59]),c_0_32]),c_0_25])])).

cnf(c_0_127,negated_conjecture,
    ( esk1_2(esk6_0,u1_struct_0(esk7_0)) = u1_struct_0(esk7_0)
    | v1_tdlat_3(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_101]),c_0_116])).

cnf(c_0_128,negated_conjecture,
    ( X1 = u1_struct_0(esk7_0)
    | ~ r1_tarski(u1_struct_0(esk7_0),X1)
    | ~ v2_tex_2(X1,esk6_0)
    | ~ v3_tex_2(u1_struct_0(esk7_0),esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_32]),c_0_25])])).

cnf(c_0_129,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk7_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_107])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk7_0),u1_struct_0(esk8_0))
    | ~ m1_pre_topc(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_24])).

cnf(c_0_131,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_126]),c_0_112])).

cnf(c_0_132,negated_conjecture,
    ( v1_tdlat_3(esk8_0)
    | v3_tex_2(u1_struct_0(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_127]),c_0_59]),c_0_32]),c_0_25])])).

cnf(c_0_133,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    | ~ v1_tdlat_3(esk7_0)
    | ~ v4_tex_2(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_134,negated_conjecture,
    ( X1 = u1_struct_0(esk7_0)
    | v1_xboole_0(u1_struct_0(esk7_0))
    | ~ r1_tarski(u1_struct_0(esk7_0),X1)
    | ~ v2_tex_2(X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_135,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk8_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_121]),c_0_25])])).

cnf(c_0_136,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk7_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_131])])).

cnf(c_0_137,negated_conjecture,
    ( v1_tdlat_3(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_132]),c_0_116])).

cnf(c_0_138,negated_conjecture,
    ( ~ v4_tex_2(esk7_0,esk6_0)
    | ~ v2_struct_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_54])])).

cnf(c_0_139,negated_conjecture,
    ( u1_struct_0(esk8_0) = u1_struct_0(esk7_0)
    | v1_xboole_0(u1_struct_0(esk7_0))
    | ~ v2_tex_2(u1_struct_0(esk8_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_136])])).

cnf(c_0_140,negated_conjecture,
    ( v2_struct_0(esk8_0)
    | v2_tex_2(u1_struct_0(esk8_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_121]),c_0_137]),c_0_25])]),c_0_27])).

cnf(c_0_141,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | ~ v2_struct_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_138,c_0_107])).

cnf(c_0_142,negated_conjecture,
    ( u1_struct_0(esk8_0) = u1_struct_0(esk7_0)
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_141])).

cnf(c_0_143,negated_conjecture,
    ( u1_struct_0(esk8_0) = u1_struct_0(esk7_0)
    | X1 = u1_struct_0(esk7_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_142])).

cnf(c_0_144,negated_conjecture,
    ( esk1_2(esk6_0,u1_struct_0(esk7_0)) = u1_struct_0(esk7_0)
    | u1_struct_0(esk8_0) = u1_struct_0(esk7_0)
    | v4_tex_2(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_143,c_0_101])).

cnf(c_0_145,negated_conjecture,
    ( u1_struct_0(esk8_0) = u1_struct_0(esk7_0)
    | v4_tex_2(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_144]),c_0_59]),c_0_32]),c_0_25])]),c_0_88])).

cnf(c_0_146,negated_conjecture,
    ( u1_struct_0(esk8_0) = u1_struct_0(esk7_0)
    | v3_tex_2(u1_struct_0(esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_145])).

cnf(c_0_147,negated_conjecture,
    ( m1_pre_topc(esk5_2(esk6_0,u1_struct_0(esk7_0)),esk6_0)
    | v1_xboole_0(u1_struct_0(esk7_0))
    | ~ v2_tex_2(u1_struct_0(esk7_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_32]),c_0_65]),c_0_25])]),c_0_27])).

cnf(c_0_148,plain,
    ( v1_pre_topc(esk5_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_149,plain,(
    ! [X42,X43,X44] :
      ( ~ l1_pre_topc(X42)
      | ~ m1_pre_topc(X43,X42)
      | ~ m1_pre_topc(X44,X42)
      | u1_struct_0(X43) != u1_struct_0(X44)
      | g1_pre_topc(u1_struct_0(X43),u1_pre_topc(X43)) = g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_tsep_1])])])).

cnf(c_0_150,negated_conjecture,
    ( u1_struct_0(esk5_2(esk6_0,u1_struct_0(esk7_0))) = u1_struct_0(esk7_0)
    | v1_xboole_0(u1_struct_0(esk7_0))
    | ~ v2_tex_2(u1_struct_0(esk7_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_32]),c_0_65]),c_0_25])]),c_0_27])).

cnf(c_0_151,negated_conjecture,
    ( u1_struct_0(esk8_0) = u1_struct_0(esk7_0)
    | X1 = u1_struct_0(esk7_0)
    | ~ r1_tarski(u1_struct_0(esk7_0),X1)
    | ~ v2_tex_2(X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_128,c_0_146])).

cnf(c_0_152,negated_conjecture,
    ( m1_pre_topc(esk5_2(esk6_0,u1_struct_0(esk7_0)),esk6_0)
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_147,c_0_59])])).

cnf(c_0_153,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v1_pre_topc(esk5_2(esk6_0,u1_struct_0(esk7_0)))
    | ~ v2_tex_2(u1_struct_0(esk7_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_32]),c_0_65]),c_0_25])]),c_0_27])).

cnf(c_0_154,plain,
    ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | u1_struct_0(X2) != u1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_149])).

cnf(c_0_155,negated_conjecture,
    ( u1_struct_0(esk5_2(esk6_0,u1_struct_0(esk7_0))) = u1_struct_0(esk7_0)
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_150,c_0_59])])).

cnf(c_0_156,negated_conjecture,
    ( u1_struct_0(esk8_0) = u1_struct_0(esk7_0)
    | ~ v2_tex_2(u1_struct_0(esk8_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_135]),c_0_136])])).

cnf(c_0_157,negated_conjecture,
    ( u1_struct_0(esk8_0) = u1_struct_0(esk7_0)
    | ~ v2_struct_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_138,c_0_145])).

cnf(c_0_158,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | l1_pre_topc(esk5_2(esk6_0,u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_152]),c_0_25])])).

cnf(c_0_159,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v1_pre_topc(esk5_2(esk6_0,u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_153,c_0_59])])).

cnf(c_0_160,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk5_2(esk6_0,u1_struct_0(esk7_0)))) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | v1_xboole_0(u1_struct_0(esk7_0))
    | u1_struct_0(esk7_0) != u1_struct_0(X1)
    | ~ m1_pre_topc(esk5_2(esk6_0,u1_struct_0(esk7_0)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_154,c_0_155])).

cnf(c_0_161,negated_conjecture,
    ( m1_pre_topc(X1,esk7_0)
    | ~ m1_pre_topc(X1,esk6_0)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_24]),c_0_65]),c_0_25])])).

cnf(c_0_162,negated_conjecture,
    ( u1_struct_0(esk8_0) = u1_struct_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_140]),c_0_157])).

cnf(c_0_163,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk5_2(esk6_0,u1_struct_0(esk7_0))),u1_pre_topc(esk5_2(esk6_0,u1_struct_0(esk7_0)))) = esk5_2(esk6_0,u1_struct_0(esk7_0))
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_158]),c_0_159])).

cnf(c_0_164,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk5_2(esk6_0,u1_struct_0(esk7_0)))) = g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))
    | v1_xboole_0(u1_struct_0(esk7_0))
    | ~ m1_pre_topc(esk5_2(esk6_0,u1_struct_0(esk7_0)),X1)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_160])).

cnf(c_0_165,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | u1_struct_0(esk7_0) != u1_struct_0(X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_84]),c_0_67])).

cnf(c_0_166,negated_conjecture,
    ( m1_pre_topc(esk8_0,esk7_0)
    | ~ r1_tarski(u1_struct_0(esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_161,c_0_121])).

cnf(c_0_167,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk7_0),u1_struct_0(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_136,c_0_162])).

cnf(c_0_168,negated_conjecture,
    ( m1_pre_topc(esk5_2(esk6_0,u1_struct_0(esk7_0)),esk7_0)
    | v1_xboole_0(u1_struct_0(esk7_0))
    | ~ r1_tarski(u1_struct_0(esk5_2(esk6_0,u1_struct_0(esk7_0))),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_161,c_0_152])).

cnf(c_0_169,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk5_2(esk6_0,u1_struct_0(esk7_0)))) = esk5_2(esk6_0,u1_struct_0(esk7_0))
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_163,c_0_155])).

cnf(c_0_170,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk5_2(esk6_0,u1_struct_0(esk7_0)))) = g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_24]),c_0_25])]),c_0_152])).

cnf(c_0_171,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk8_0)) = g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)),X1)
    | ~ m1_pre_topc(esk8_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_165,c_0_162])).

cnf(c_0_172,negated_conjecture,
    ( m1_pre_topc(esk8_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_166,c_0_162]),c_0_167])])).

cnf(c_0_173,negated_conjecture,
    ( m1_pre_topc(esk5_2(esk6_0,u1_struct_0(esk7_0)),esk7_0)
    | v1_xboole_0(u1_struct_0(esk7_0))
    | ~ r1_tarski(u1_struct_0(esk7_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_168,c_0_155])).

cnf(c_0_174,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) != g1_pre_topc(u1_struct_0(esk8_0),u1_pre_topc(esk8_0))
    | ~ v1_tdlat_3(esk7_0)
    | ~ v4_tex_2(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_175,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) = esk5_2(esk6_0,u1_struct_0(esk7_0))
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_169,c_0_170])).

cnf(c_0_176,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk8_0)) = g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_172]),c_0_37])])).

cnf(c_0_177,negated_conjecture,
    ( m1_pre_topc(esk5_2(esk6_0,u1_struct_0(esk7_0)),esk7_0)
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_173,c_0_167])])).

cnf(c_0_178,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk8_0),u1_pre_topc(esk8_0)) != g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))
    | ~ v4_tex_2(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_174,c_0_54])])).

cnf(c_0_179,negated_conjecture,
    ( u1_pre_topc(esk7_0) = X1
    | v1_xboole_0(u1_struct_0(esk7_0))
    | esk5_2(esk6_0,u1_struct_0(esk7_0)) != g1_pre_topc(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_175]),c_0_43])])).

cnf(c_0_180,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk8_0)) = esk5_2(esk6_0,u1_struct_0(esk7_0))
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_175]),c_0_177])).

cnf(c_0_181,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk8_0)) != g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))
    | ~ v4_tex_2(esk7_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_178,c_0_162])).

cnf(c_0_182,negated_conjecture,
    ( u1_pre_topc(esk8_0) = u1_pre_topc(esk7_0)
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_179,c_0_180])).

cnf(c_0_183,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_182]),c_0_107])).

cnf(c_0_184,negated_conjecture,
    ( X1 = u1_struct_0(esk7_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_183])).

cnf(c_0_185,negated_conjecture,
    ( esk1_2(esk6_0,u1_struct_0(esk7_0)) = u1_struct_0(esk7_0)
    | v4_tex_2(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_184,c_0_101])).

cnf(c_0_186,negated_conjecture,
    ( v4_tex_2(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_185]),c_0_59]),c_0_32]),c_0_25])]),c_0_88])).

cnf(c_0_187,negated_conjecture,
    ( m1_pre_topc(X1,esk8_0)
    | ~ m1_pre_topc(X1,esk6_0)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_121]),c_0_65]),c_0_25])])).

cnf(c_0_188,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk8_0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | u1_struct_0(esk7_0) != u1_struct_0(X1)
    | ~ m1_pre_topc(esk8_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_154,c_0_162])).

cnf(c_0_189,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk8_0)) != g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_181,c_0_186])])).

cnf(c_0_190,negated_conjecture,
    ( m1_pre_topc(esk8_0,esk8_0)
    | ~ r1_tarski(u1_struct_0(esk8_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_187,c_0_121])).

cnf(c_0_191,negated_conjecture,
    ( ~ m1_pre_topc(esk8_0,X1)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_188]),c_0_189])).

cnf(c_0_192,negated_conjecture,
    ( m1_pre_topc(esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_190,c_0_162]),c_0_162]),c_0_167])])).

cnf(c_0_193,negated_conjecture,
    ( l1_pre_topc(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_121]),c_0_25])])).

cnf(c_0_194,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_192]),c_0_131]),c_0_193])]),
    [proof]).

%------------------------------------------------------------------------------
