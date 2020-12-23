%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1866+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:09 EST 2020

% Result     : Theorem 15.29s
% Output     : CNFRefutation 15.30s
% Verified   : 
% Statistics : Number of formulae       :   29 ( 166 expanded)
%              Number of clauses        :   20 (  52 expanded)
%              Number of leaves         :    4 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :  146 (1381 expanded)
%              Number of equality atoms :   12 ( 119 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_tex_2,conjecture,(
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

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT028+2.ax',t1_tsep_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t34_tex_2])).

fof(c_0_5,plain,(
    ! [X11766,X11767] :
      ( ( ~ v2_struct_0(esk1347_2(X11766,X11767))
        | v1_xboole_0(X11767)
        | ~ m1_subset_1(X11767,k1_zfmisc_1(u1_struct_0(X11766)))
        | v2_struct_0(X11766)
        | ~ l1_pre_topc(X11766) )
      & ( v1_pre_topc(esk1347_2(X11766,X11767))
        | v1_xboole_0(X11767)
        | ~ m1_subset_1(X11767,k1_zfmisc_1(u1_struct_0(X11766)))
        | v2_struct_0(X11766)
        | ~ l1_pre_topc(X11766) )
      & ( m1_pre_topc(esk1347_2(X11766,X11767),X11766)
        | v1_xboole_0(X11767)
        | ~ m1_subset_1(X11767,k1_zfmisc_1(u1_struct_0(X11766)))
        | v2_struct_0(X11766)
        | ~ l1_pre_topc(X11766) )
      & ( X11767 = u1_struct_0(esk1347_2(X11766,X11767))
        | v1_xboole_0(X11767)
        | ~ m1_subset_1(X11767,k1_zfmisc_1(u1_struct_0(X11766)))
        | v2_struct_0(X11766)
        | ~ l1_pre_topc(X11766) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X11838] :
      ( ~ v2_struct_0(esk1356_0)
      & v2_pre_topc(esk1356_0)
      & l1_pre_topc(esk1356_0)
      & ~ v1_xboole_0(esk1357_0)
      & m1_subset_1(esk1357_0,k1_zfmisc_1(u1_struct_0(esk1356_0)))
      & v2_tex_2(esk1357_0,esk1356_0)
      & ( v2_struct_0(X11838)
        | ~ v1_pre_topc(X11838)
        | ~ v1_tdlat_3(X11838)
        | ~ m1_pre_topc(X11838,esk1356_0)
        | esk1357_0 != u1_struct_0(X11838) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

cnf(c_0_7,plain,
    ( X1 = u1_struct_0(esk1347_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk1357_0,k1_zfmisc_1(u1_struct_0(esk1356_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( l1_pre_topc(esk1356_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1356_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( ~ v1_xboole_0(esk1357_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_pre_topc(esk1347_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk1347_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_14,plain,(
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

fof(c_0_15,plain,(
    ! [X11076,X11077] :
      ( ~ l1_pre_topc(X11076)
      | ~ m1_pre_topc(X11077,X11076)
      | m1_subset_1(u1_struct_0(X11077),k1_zfmisc_1(u1_struct_0(X11076))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_16,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v1_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,esk1356_0)
    | esk1357_0 != u1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( u1_struct_0(esk1347_2(esk1356_0,esk1357_0)) = esk1357_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])]),c_0_10]),c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v1_pre_topc(esk1347_2(esk1356_0,esk1357_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_8]),c_0_9])]),c_0_10]),c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk1347_2(esk1356_0,esk1357_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_8]),c_0_9])]),c_0_10]),c_0_11])).

cnf(c_0_20,plain,
    ( m1_pre_topc(esk1347_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,plain,
    ( v1_tdlat_3(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | X1 != u1_struct_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_tdlat_3(esk1347_2(esk1356_0,esk1357_0))
    | ~ m1_pre_topc(esk1347_2(esk1356_0,esk1357_0),esk1356_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk1347_2(esk1356_0,esk1357_0),esk1356_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_8]),c_0_9])]),c_0_10]),c_0_11])).

cnf(c_0_25,plain,
    ( v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v2_tex_2(esk1357_0,esk1356_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_tdlat_3(esk1347_2(esk1356_0,esk1357_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_17]),c_0_26]),c_0_9])]),c_0_27]),c_0_10]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
