%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:57 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 887 expanded)
%              Number of clauses        :   58 ( 324 expanded)
%              Number of leaves         :   15 ( 218 expanded)
%              Depth                    :   13
%              Number of atoms          :  490 (8627 expanded)
%              Number of equality atoms :   41 ( 971 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal clause size      :   90 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t88_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = X4
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( ( X6 = X7
                                    & r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) )
                                 => r1_tmap_1(X4,X2,X5,X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(fc7_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_pre_topc)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(t86_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( ( v1_tsep_1(X3,X4)
                          & m1_pre_topc(X3,X4) )
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( X6 = X7
                                 => ( r1_tmap_1(X4,X2,X5,X6)
                                  <=> r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

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

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t16_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( ( v1_tsep_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                       => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = X4
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X4))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X3))
                                 => ( ( X6 = X7
                                      & r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) )
                                   => r1_tmap_1(X4,X2,X5,X6) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t88_tmap_1])).

fof(c_0_16,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_pre_topc(X21,X20)
      | l1_pre_topc(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk4_0)
    & ~ v2_struct_0(esk7_0)
    & m1_pre_topc(esk7_0,esk4_0)
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0))))
    & g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = esk7_0
    & m1_subset_1(esk9_0,u1_struct_0(esk7_0))
    & m1_subset_1(esk10_0,u1_struct_0(esk6_0))
    & esk9_0 = esk10_0
    & r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0)
    & ~ r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X23] :
      ( ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)))
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23) )
      & ( v1_pre_topc(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)))
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_pre_topc])])])])).

cnf(c_0_19,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X24,X25,X26,X27] :
      ( ( X24 = X26
        | g1_pre_topc(X24,X25) != g1_pre_topc(X26,X27)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))) )
      & ( X25 = X27
        | g1_pre_topc(X24,X25) != g1_pre_topc(X26,X27)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_23,plain,(
    ! [X22] :
      ( ~ l1_pre_topc(X22)
      | m1_subset_1(u1_pre_topc(X22),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_24,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(X8)
      | ~ v1_pre_topc(X8)
      | X8 = g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_25,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_27,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_pre_topc(esk7_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_29]),c_0_21])])).

cnf(c_0_35,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_37,negated_conjecture,
    ( u1_pre_topc(esk7_0) = X1
    | g1_pre_topc(X2,X1) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_34])])).

fof(c_0_38,plain,(
    ! [X28,X29] :
      ( ( ~ m1_pre_topc(X28,X29)
        | m1_pre_topc(X28,g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))
        | ~ l1_pre_topc(X29)
        | ~ l1_pre_topc(X28) )
      & ( ~ m1_pre_topc(X28,g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))
        | m1_pre_topc(X28,X29)
        | ~ l1_pre_topc(X29)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_39,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45] :
      ( ( ~ r1_tmap_1(X42,X40,X43,X44)
        | r1_tmap_1(X41,X40,k3_tmap_1(X39,X40,X42,X41,X43),X45)
        | X44 != X45
        | ~ m1_subset_1(X45,u1_struct_0(X41))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ v1_tsep_1(X41,X42)
        | ~ m1_pre_topc(X41,X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X40))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X40))))
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X39)
        | v2_struct_0(X41)
        | ~ m1_pre_topc(X41,X39)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( ~ r1_tmap_1(X41,X40,k3_tmap_1(X39,X40,X42,X41,X43),X45)
        | r1_tmap_1(X42,X40,X43,X44)
        | X44 != X45
        | ~ m1_subset_1(X45,u1_struct_0(X41))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ v1_tsep_1(X41,X42)
        | ~ m1_pre_topc(X41,X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X40))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X40))))
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X39)
        | v2_struct_0(X41)
        | ~ m1_pre_topc(X41,X39)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t86_tmap_1])])])])])).

fof(c_0_40,plain,(
    ! [X36,X37,X38] :
      ( ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_pre_topc(X37,X36)
      | ~ m1_pre_topc(X38,X37)
      | m1_pre_topc(X38,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_41,negated_conjecture,
    ( u1_pre_topc(esk6_0) = u1_pre_topc(esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_42,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_43,plain,(
    ! [X9,X10] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | v2_pre_topc(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_44,plain,
    ( r1_tmap_1(X4,X2,X5,X7)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | X7 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | ~ v1_tsep_1(X1,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_41]),c_0_26])])).

cnf(c_0_48,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_41])).

cnf(c_0_49,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_42,c_0_19])).

fof(c_0_50,plain,(
    ! [X35] :
      ( ~ l1_pre_topc(X35)
      | m1_pre_topc(X35,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_51,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v1_tsep_1(X31,X30)
        | ~ m1_pre_topc(X31,X30)
        | v3_pre_topc(X32,X30)
        | X32 != u1_struct_0(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_pre_topc(X31,X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( v1_tsep_1(X31,X30)
        | ~ v3_pre_topc(X32,X30)
        | X32 != u1_struct_0(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_pre_topc(X31,X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( m1_pre_topc(X31,X30)
        | ~ v3_pre_topc(X32,X30)
        | X32 != u1_struct_0(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_pre_topc(X31,X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

fof(c_0_52,plain,(
    ! [X33,X34] :
      ( ~ l1_pre_topc(X33)
      | ~ m1_pre_topc(X34,X33)
      | m1_subset_1(u1_struct_0(X34),k1_zfmisc_1(u1_struct_0(X33))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_53,plain,(
    ! [X11,X12,X13,X14] :
      ( ( r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ r1_tarski(X12,u1_pre_topc(X11))
        | r2_hidden(k5_setfam_1(u1_struct_0(X11),X12),u1_pre_topc(X11))
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ r2_hidden(X13,u1_pre_topc(X11))
        | ~ r2_hidden(X14,u1_pre_topc(X11))
        | r2_hidden(k9_subset_1(u1_struct_0(X11),X13,X14),u1_pre_topc(X11))
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk2_1(X11),k1_zfmisc_1(u1_struct_0(X11)))
        | m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk3_1(X11),k1_zfmisc_1(u1_struct_0(X11)))
        | m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( r2_hidden(esk2_1(X11),u1_pre_topc(X11))
        | m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( r2_hidden(esk3_1(X11),u1_pre_topc(X11))
        | m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X11),esk2_1(X11),esk3_1(X11)),u1_pre_topc(X11))
        | m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk2_1(X11),k1_zfmisc_1(u1_struct_0(X11)))
        | r1_tarski(esk1_1(X11),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk3_1(X11),k1_zfmisc_1(u1_struct_0(X11)))
        | r1_tarski(esk1_1(X11),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( r2_hidden(esk2_1(X11),u1_pre_topc(X11))
        | r1_tarski(esk1_1(X11),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( r2_hidden(esk3_1(X11),u1_pre_topc(X11))
        | r1_tarski(esk1_1(X11),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X11),esk2_1(X11),esk3_1(X11)),u1_pre_topc(X11))
        | r1_tarski(esk1_1(X11),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk2_1(X11),k1_zfmisc_1(u1_struct_0(X11)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk3_1(X11),k1_zfmisc_1(u1_struct_0(X11)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( r2_hidden(esk2_1(X11),u1_pre_topc(X11))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( r2_hidden(esk3_1(X11),u1_pre_topc(X11))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X11),esk2_1(X11),esk3_1(X11)),u1_pre_topc(X11))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_54,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_56,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ v1_tsep_1(X6,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X6))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X6,X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_60,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_61,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_62,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_63,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_64,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_65,negated_conjecture,
    ( esk9_0 = esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(esk6_0) = X1
    | g1_pre_topc(X1,X2) != esk7_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_67,negated_conjecture,
    ( m1_pre_topc(X1,esk7_0)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_27]),c_0_26])])).

cnf(c_0_68,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_69,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_70,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_71,plain,(
    ! [X18,X19] :
      ( ( ~ v3_pre_topc(X19,X18)
        | r2_hidden(X19,u1_pre_topc(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( ~ r2_hidden(X19,u1_pre_topc(X18))
        | v3_pre_topc(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_72,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_73,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_20]),c_0_55]),c_0_21])])).

cnf(c_0_74,negated_conjecture,
    ( r1_tmap_1(esk7_0,esk5_0,esk8_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X3,esk5_0,k3_tmap_1(X2,esk5_0,esk7_0,X3,esk8_0),X1)
    | ~ v1_tsep_1(X3,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_pre_topc(esk7_0,X2)
    | ~ m1_pre_topc(X3,esk7_0)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_61])]),c_0_62]),c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk6_0) = u1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_36])).

cnf(c_0_78,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_26])])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_80,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_81,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_69]),c_0_70])).

cnf(c_0_82,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_41]),c_0_73]),c_0_26])])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_tsep_1(esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_77]),c_0_76]),c_0_29]),c_0_78]),c_0_55]),c_0_21])]),c_0_79]),c_0_80]),c_0_28])).

cnf(c_0_85,plain,
    ( v1_tsep_1(X1,X2)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_70])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_83,c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_29]),c_0_55]),c_0_21])])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_77]),c_0_86]),c_0_78]),c_0_87]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:13:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.031 s
% 0.21/0.41  # Presaturation interreduction done
% 0.21/0.41  
% 0.21/0.41  # Proof found!
% 0.21/0.41  # SZS status Theorem
% 0.21/0.41  # SZS output start CNFRefutation
% 0.21/0.41  fof(t88_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 0.21/0.41  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.41  fof(fc7_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>(~(v2_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))&v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_pre_topc)).
% 0.21/0.41  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.21/0.41  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.21/0.41  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.21/0.41  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.21/0.41  fof(t86_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((v1_tsep_1(X3,X4)&m1_pre_topc(X3,X4))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(X6=X7=>(r1_tmap_1(X4,X2,X5,X6)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 0.21/0.41  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.21/0.41  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.21/0.41  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.21/0.41  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.21/0.41  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.21/0.41  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.21/0.41  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.21/0.41  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6))))))))))), inference(assume_negation,[status(cth)],[t88_tmap_1])).
% 0.21/0.41  fof(c_0_16, plain, ![X20, X21]:(~l1_pre_topc(X20)|(~m1_pre_topc(X21,X20)|l1_pre_topc(X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.41  fof(c_0_17, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk4_0))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk4_0))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0)))))&(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))=esk7_0&(m1_subset_1(esk9_0,u1_struct_0(esk7_0))&(m1_subset_1(esk10_0,u1_struct_0(esk6_0))&((esk9_0=esk10_0&r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0))&~r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.21/0.41  fof(c_0_18, plain, ![X23]:((~v2_struct_0(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)))|(v2_struct_0(X23)|~l1_pre_topc(X23)))&(v1_pre_topc(g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)))|(v2_struct_0(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_pre_topc])])])])).
% 0.21/0.41  cnf(c_0_19, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_20, negated_conjecture, (m1_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  fof(c_0_22, plain, ![X24, X25, X26, X27]:((X24=X26|g1_pre_topc(X24,X25)!=g1_pre_topc(X26,X27)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))))&(X25=X27|g1_pre_topc(X24,X25)!=g1_pre_topc(X26,X27)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.21/0.41  fof(c_0_23, plain, ![X22]:(~l1_pre_topc(X22)|m1_subset_1(u1_pre_topc(X22),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.21/0.41  fof(c_0_24, plain, ![X8]:(~l1_pre_topc(X8)|(~v1_pre_topc(X8)|X8=g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.21/0.41  cnf(c_0_25, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|v2_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.41  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.21/0.41  cnf(c_0_27, negated_conjecture, (g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))=esk7_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_30, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.41  cnf(c_0_31, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.41  cnf(c_0_32, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.41  cnf(c_0_33, negated_conjecture, (v1_pre_topc(esk7_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])).
% 0.21/0.41  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_29]), c_0_21])])).
% 0.21/0.41  cnf(c_0_35, plain, (u1_pre_topc(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X3,X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.41  cnf(c_0_36, negated_conjecture, (g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.21/0.41  cnf(c_0_37, negated_conjecture, (u1_pre_topc(esk7_0)=X1|g1_pre_topc(X2,X1)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_34])])).
% 0.21/0.41  fof(c_0_38, plain, ![X28, X29]:((~m1_pre_topc(X28,X29)|m1_pre_topc(X28,g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))|~l1_pre_topc(X29)|~l1_pre_topc(X28))&(~m1_pre_topc(X28,g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))|m1_pre_topc(X28,X29)|~l1_pre_topc(X29)|~l1_pre_topc(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.21/0.41  fof(c_0_39, plain, ![X39, X40, X41, X42, X43, X44, X45]:((~r1_tmap_1(X42,X40,X43,X44)|r1_tmap_1(X41,X40,k3_tmap_1(X39,X40,X42,X41,X43),X45)|X44!=X45|~m1_subset_1(X45,u1_struct_0(X41))|~m1_subset_1(X44,u1_struct_0(X42))|(~v1_tsep_1(X41,X42)|~m1_pre_topc(X41,X42))|(~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X40))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X40)))))|(v2_struct_0(X42)|~m1_pre_topc(X42,X39))|(v2_struct_0(X41)|~m1_pre_topc(X41,X39))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(~r1_tmap_1(X41,X40,k3_tmap_1(X39,X40,X42,X41,X43),X45)|r1_tmap_1(X42,X40,X43,X44)|X44!=X45|~m1_subset_1(X45,u1_struct_0(X41))|~m1_subset_1(X44,u1_struct_0(X42))|(~v1_tsep_1(X41,X42)|~m1_pre_topc(X41,X42))|(~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X40))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X40)))))|(v2_struct_0(X42)|~m1_pre_topc(X42,X39))|(v2_struct_0(X41)|~m1_pre_topc(X41,X39))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t86_tmap_1])])])])])).
% 0.21/0.41  fof(c_0_40, plain, ![X36, X37, X38]:(~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~m1_pre_topc(X37,X36)|(~m1_pre_topc(X38,X37)|m1_pre_topc(X38,X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.21/0.41  cnf(c_0_41, negated_conjecture, (u1_pre_topc(esk6_0)=u1_pre_topc(esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 0.21/0.41  cnf(c_0_42, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.41  fof(c_0_43, plain, ![X9, X10]:(~v2_pre_topc(X9)|~l1_pre_topc(X9)|(~m1_pre_topc(X10,X9)|v2_pre_topc(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.21/0.41  cnf(c_0_44, plain, (r1_tmap_1(X4,X2,X5,X7)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|X7!=X6|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(X4))|~v1_tsep_1(X1,X4)|~m1_pre_topc(X1,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.41  cnf(c_0_45, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.41  cnf(c_0_46, plain, (X1=X2|g1_pre_topc(X1,X3)!=g1_pre_topc(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.41  cnf(c_0_47, negated_conjecture, (m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_41]), c_0_26])])).
% 0.21/0.41  cnf(c_0_48, negated_conjecture, (g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk7_0))=esk7_0), inference(rw,[status(thm)],[c_0_27, c_0_41])).
% 0.21/0.41  cnf(c_0_49, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_42, c_0_19])).
% 0.21/0.41  fof(c_0_50, plain, ![X35]:(~l1_pre_topc(X35)|m1_pre_topc(X35,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.21/0.41  fof(c_0_51, plain, ![X30, X31, X32]:((~v1_tsep_1(X31,X30)|~m1_pre_topc(X31,X30)|v3_pre_topc(X32,X30)|X32!=u1_struct_0(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_pre_topc(X31,X30)|(~v2_pre_topc(X30)|~l1_pre_topc(X30)))&((v1_tsep_1(X31,X30)|~v3_pre_topc(X32,X30)|X32!=u1_struct_0(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_pre_topc(X31,X30)|(~v2_pre_topc(X30)|~l1_pre_topc(X30)))&(m1_pre_topc(X31,X30)|~v3_pre_topc(X32,X30)|X32!=u1_struct_0(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_pre_topc(X31,X30)|(~v2_pre_topc(X30)|~l1_pre_topc(X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.21/0.41  fof(c_0_52, plain, ![X33, X34]:(~l1_pre_topc(X33)|(~m1_pre_topc(X34,X33)|m1_subset_1(u1_struct_0(X34),k1_zfmisc_1(u1_struct_0(X33))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.21/0.41  fof(c_0_53, plain, ![X11, X12, X13, X14]:((((r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))|~v2_pre_topc(X11)|~l1_pre_topc(X11))&(~m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))|(~r1_tarski(X12,u1_pre_topc(X11))|r2_hidden(k5_setfam_1(u1_struct_0(X11),X12),u1_pre_topc(X11)))|~v2_pre_topc(X11)|~l1_pre_topc(X11)))&(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X11)))|(~r2_hidden(X13,u1_pre_topc(X11))|~r2_hidden(X14,u1_pre_topc(X11))|r2_hidden(k9_subset_1(u1_struct_0(X11),X13,X14),u1_pre_topc(X11))))|~v2_pre_topc(X11)|~l1_pre_topc(X11)))&(((m1_subset_1(esk2_1(X11),k1_zfmisc_1(u1_struct_0(X11)))|(m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&((m1_subset_1(esk3_1(X11),k1_zfmisc_1(u1_struct_0(X11)))|(m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&(((r2_hidden(esk2_1(X11),u1_pre_topc(X11))|(m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&(r2_hidden(esk3_1(X11),u1_pre_topc(X11))|(m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11)))&(~r2_hidden(k9_subset_1(u1_struct_0(X11),esk2_1(X11),esk3_1(X11)),u1_pre_topc(X11))|(m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11)))))&(((m1_subset_1(esk2_1(X11),k1_zfmisc_1(u1_struct_0(X11)))|(r1_tarski(esk1_1(X11),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&((m1_subset_1(esk3_1(X11),k1_zfmisc_1(u1_struct_0(X11)))|(r1_tarski(esk1_1(X11),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&(((r2_hidden(esk2_1(X11),u1_pre_topc(X11))|(r1_tarski(esk1_1(X11),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&(r2_hidden(esk3_1(X11),u1_pre_topc(X11))|(r1_tarski(esk1_1(X11),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11)))&(~r2_hidden(k9_subset_1(u1_struct_0(X11),esk2_1(X11),esk3_1(X11)),u1_pre_topc(X11))|(r1_tarski(esk1_1(X11),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11)))))&((m1_subset_1(esk2_1(X11),k1_zfmisc_1(u1_struct_0(X11)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&((m1_subset_1(esk3_1(X11),k1_zfmisc_1(u1_struct_0(X11)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&(((r2_hidden(esk2_1(X11),u1_pre_topc(X11))|(~r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&(r2_hidden(esk3_1(X11),u1_pre_topc(X11))|(~r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11)))&(~r2_hidden(k9_subset_1(u1_struct_0(X11),esk2_1(X11),esk3_1(X11)),u1_pre_topc(X11))|(~r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.21/0.41  cnf(c_0_54, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.41  cnf(c_0_55, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_56, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X5)|v2_struct_0(X2)|v2_struct_0(X6)|~r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~v1_tsep_1(X6,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X6))|~m1_pre_topc(X1,X5)|~m1_pre_topc(X6,X1)|~v2_pre_topc(X5)|~v2_pre_topc(X2)|~l1_pre_topc(X5)|~l1_pre_topc(X2)), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_44, c_0_45])])).
% 0.21/0.41  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_58, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_59, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_60, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_61, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_62, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_63, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_64, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_65, negated_conjecture, (esk9_0=esk10_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_66, negated_conjecture, (u1_struct_0(esk6_0)=X1|g1_pre_topc(X1,X2)!=esk7_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.21/0.41  cnf(c_0_67, negated_conjecture, (m1_pre_topc(X1,esk7_0)|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_27]), c_0_26])])).
% 0.21/0.41  cnf(c_0_68, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.41  cnf(c_0_69, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.41  cnf(c_0_70, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.41  fof(c_0_71, plain, ![X18, X19]:((~v3_pre_topc(X19,X18)|r2_hidden(X19,u1_pre_topc(X18))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&(~r2_hidden(X19,u1_pre_topc(X18))|v3_pre_topc(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.21/0.41  cnf(c_0_72, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.41  cnf(c_0_73, negated_conjecture, (v2_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_20]), c_0_55]), c_0_21])])).
% 0.21/0.41  cnf(c_0_74, negated_conjecture, (r1_tmap_1(esk7_0,esk5_0,esk8_0,X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X3,esk5_0,k3_tmap_1(X2,esk5_0,esk7_0,X3,esk8_0),X1)|~v1_tsep_1(X3,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(X3))|~m1_pre_topc(esk7_0,X2)|~m1_pre_topc(X3,esk7_0)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_59]), c_0_60]), c_0_61])]), c_0_62]), c_0_63])).
% 0.21/0.41  cnf(c_0_75, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk9_0)), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.41  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_77, negated_conjecture, (u1_struct_0(esk6_0)=u1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_66, c_0_36])).
% 0.21/0.41  cnf(c_0_78, negated_conjecture, (m1_pre_topc(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_26])])).
% 0.21/0.41  cnf(c_0_79, negated_conjecture, (~r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_80, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_81, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_69]), c_0_70])).
% 0.21/0.41  cnf(c_0_82, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.21/0.41  cnf(c_0_83, negated_conjecture, (r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_41]), c_0_73]), c_0_26])])).
% 0.21/0.41  cnf(c_0_84, negated_conjecture, (~v1_tsep_1(esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_77]), c_0_76]), c_0_29]), c_0_78]), c_0_55]), c_0_21])]), c_0_79]), c_0_80]), c_0_28])).
% 0.21/0.41  cnf(c_0_85, plain, (v1_tsep_1(X1,X2)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_70])).
% 0.21/0.41  cnf(c_0_86, negated_conjecture, (r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))), inference(rw,[status(thm)],[c_0_83, c_0_77])).
% 0.21/0.41  cnf(c_0_87, negated_conjecture, (v2_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_29]), c_0_55]), c_0_21])])).
% 0.21/0.41  cnf(c_0_88, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_77]), c_0_86]), c_0_78]), c_0_87]), c_0_34])]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 89
% 0.21/0.41  # Proof object clause steps            : 58
% 0.21/0.41  # Proof object formula steps           : 31
% 0.21/0.41  # Proof object conjectures             : 41
% 0.21/0.41  # Proof object clause conjectures      : 38
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 33
% 0.21/0.41  # Proof object initial formulas used   : 15
% 0.21/0.41  # Proof object generating inferences   : 19
% 0.21/0.41  # Proof object simplifying inferences  : 59
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 15
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 57
% 0.21/0.41  # Removed in clause preprocessing      : 1
% 0.21/0.41  # Initial clauses in saturation        : 56
% 0.21/0.41  # Processed clauses                    : 426
% 0.21/0.41  # ...of these trivial                  : 9
% 0.21/0.41  # ...subsumed                          : 160
% 0.21/0.41  # ...remaining for further processing  : 257
% 0.21/0.41  # Other redundant clauses eliminated   : 4
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 6
% 0.21/0.41  # Backward-rewritten                   : 11
% 0.21/0.41  # Generated clauses                    : 751
% 0.21/0.41  # ...of the previous two non-trivial   : 455
% 0.21/0.41  # Contextual simplify-reflections      : 44
% 0.21/0.41  # Paramodulations                      : 745
% 0.21/0.41  # Factorizations                       : 0
% 0.21/0.41  # Equation resolutions                 : 6
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 180
% 0.21/0.41  #    Positive orientable unit clauses  : 29
% 0.21/0.41  #    Positive unorientable unit clauses: 0
% 0.21/0.41  #    Negative unit clauses             : 6
% 0.21/0.41  #    Non-unit-clauses                  : 145
% 0.21/0.41  # Current number of unprocessed clauses: 132
% 0.21/0.41  # ...number of literals in the above   : 811
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 73
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 9128
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 1944
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 207
% 0.21/0.41  # Unit Clause-clause subsumption calls : 159
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 9
% 0.21/0.41  # BW rewrite match successes           : 5
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 24518
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.067 s
% 0.21/0.41  # System time              : 0.004 s
% 0.21/0.41  # Total time               : 0.070 s
% 0.21/0.41  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
