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
% DateTime   : Thu Dec  3 11:17:14 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 (1028 expanded)
%              Number of clauses        :   68 ( 374 expanded)
%              Number of leaves         :   16 ( 251 expanded)
%              Depth                    :   18
%              Number of atoms          :  395 (9936 expanded)
%              Number of equality atoms :   31 ( 496 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   25 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_tmap_1,conjecture,(
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
                & m1_pre_topc(X3,X2) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                     => ( ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X2))
                           => ( r2_hidden(X6,u1_struct_0(X3))
                             => k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                       => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d9_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r2_funct_2(X1,X2,X3,X4)
          <=> ! [X5] :
                ( m1_subset_1(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).

fof(dt_k2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & l1_struct_0(X4) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(d4_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t72_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,X2)
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_16,negated_conjecture,(
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
                  & m1_pre_topc(X3,X2) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                       => ( ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( r2_hidden(X6,u1_struct_0(X3))
                               => k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                         => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_tmap_1])).

fof(c_0_17,plain,(
    ! [X39] :
      ( ~ l1_pre_topc(X39)
      | l1_struct_0(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_18,negated_conjecture,(
    ! [X58] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & l1_pre_topc(esk4_0)
      & ~ v2_struct_0(esk5_0)
      & m1_pre_topc(esk5_0,esk4_0)
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
      & v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))
      & ( ~ m1_subset_1(X58,u1_struct_0(esk4_0))
        | ~ r2_hidden(X58,u1_struct_0(esk5_0))
        | k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,X58) = k1_funct_1(esk7_0,X58) )
      & ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).

fof(c_0_19,plain,(
    ! [X40,X41] :
      ( ~ l1_pre_topc(X40)
      | ~ m1_pre_topc(X41,X40)
      | l1_pre_topc(X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_20,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( ( ~ r2_funct_2(X25,X26,X27,X28)
        | ~ m1_subset_1(X29,X25)
        | k1_funct_1(X27,X29) = k1_funct_1(X28,X29)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X25,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( m1_subset_1(esk2_4(X25,X26,X27,X28),X25)
        | r2_funct_2(X25,X26,X27,X28)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X25,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( k1_funct_1(X27,esk2_4(X25,X26,X27,X28)) != k1_funct_1(X28,esk2_4(X25,X26,X27,X28))
        | r2_funct_2(X25,X26,X27,X28)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X25,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).

fof(c_0_21,plain,(
    ! [X47,X48,X49,X50] :
      ( ( v1_funct_1(k2_tmap_1(X47,X48,X49,X50))
        | ~ l1_struct_0(X47)
        | ~ l1_struct_0(X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | ~ l1_struct_0(X50) )
      & ( v1_funct_2(k2_tmap_1(X47,X48,X49,X50),u1_struct_0(X50),u1_struct_0(X48))
        | ~ l1_struct_0(X47)
        | ~ l1_struct_0(X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | ~ l1_struct_0(X50) )
      & ( m1_subset_1(k2_tmap_1(X47,X48,X49,X50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X48))))
        | ~ l1_struct_0(X47)
        | ~ l1_struct_0(X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | ~ l1_struct_0(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_22,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),X1)
    | r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_24])])).

cnf(c_0_38,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),X1,esk7_0)
    | m1_subset_1(esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),X1,esk7_0),u1_struct_0(esk5_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk5_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk4_0,esk3_0,esk6_0,X1),u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_40,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0),u1_struct_0(esk5_0))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,X1))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_45,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_46,plain,(
    ! [X43,X44,X45,X46] :
      ( v2_struct_0(X43)
      | ~ v2_pre_topc(X43)
      | ~ l1_pre_topc(X43)
      | v2_struct_0(X44)
      | ~ v2_pre_topc(X44)
      | ~ l1_pre_topc(X44)
      | ~ v1_funct_1(X45)
      | ~ v1_funct_2(X45,u1_struct_0(X43),u1_struct_0(X44))
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X44))))
      | ~ m1_pre_topc(X46,X43)
      | k2_tmap_1(X43,X44,X45,X46) = k2_partfun1(u1_struct_0(X43),u1_struct_0(X44),X45,u1_struct_0(X46)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

fof(c_0_47,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X11,X12)
      | v1_xboole_0(X12)
      | r2_hidden(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_40])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_53,plain,(
    ! [X31,X32,X33,X34] :
      ( ~ v1_funct_1(X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k2_partfun1(X31,X32,X33,X34) = k7_relat_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_54,plain,(
    ! [X13,X14,X15] :
      ( ~ r2_hidden(X13,X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X15))
      | m1_subset_1(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_40])])).

fof(c_0_57,plain,(
    ! [X51,X52] :
      ( ~ l1_pre_topc(X51)
      | ~ m1_pre_topc(X52,X51)
      | m1_subset_1(u1_struct_0(X52),k1_zfmisc_1(u1_struct_0(X51))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_58,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | ~ v1_xboole_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_59,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_60,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | ~ r2_hidden(X19,X20)
      | k1_funct_1(k7_relat_1(X21,X20),X19) = k1_funct_1(X21,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).

cnf(c_0_61,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(X1),X2,u1_struct_0(esk5_0)) = k2_tmap_1(esk4_0,X1,X2,esk5_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_26]),c_0_51]),c_0_24])]),c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_63,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_64,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_65,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | v1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0),u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_68,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_69,plain,(
    ! [X35,X36,X37,X38] :
      ( v1_xboole_0(X35)
      | ~ v1_funct_1(X37)
      | ~ v1_funct_2(X37,X35,X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | ~ m1_subset_1(X38,X35)
      | k3_funct_2(X35,X36,X37,X38) = k1_funct_1(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_71,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0)) = k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_32]),c_0_62]),c_0_23]),c_0_35]),c_0_36])]),c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,X1) = k7_relat_1(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_36]),c_0_35])])).

cnf(c_0_75,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0),X1)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_26]),c_0_24])])).

cnf(c_0_78,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_80,negated_conjecture,
    ( k1_funct_1(k7_relat_1(X1,u1_struct_0(esk5_0)),esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0)) = k1_funct_1(X1,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_67])).

cnf(c_0_81,negated_conjecture,
    ( k7_relat_1(esk6_0,u1_struct_0(esk5_0)) = k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_36])).

cnf(c_0_83,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,X1) = k1_funct_1(esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,X1) = k1_funct_1(esk6_0,X1)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_32]),c_0_35]),c_0_36])])).

cnf(c_0_86,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_77])).

cnf(c_0_87,plain,
    ( r2_funct_2(X2,X3,X1,X4)
    | k1_funct_1(X1,esk2_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk2_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_88,negated_conjecture,
    ( k1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0)) = k1_funct_1(esk6_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_35]),c_0_82])])).

cnf(c_0_89,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0)) = k1_funct_1(esk7_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_67]),c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0)) = k1_funct_1(esk6_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_84]),c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | k1_funct_1(esk6_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0)) != k1_funct_1(esk7_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))
    | ~ v1_funct_2(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_28]),c_0_29]),c_0_30])]),c_0_41])).

cnf(c_0_92,negated_conjecture,
    ( k1_funct_1(esk6_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0)) = k1_funct_1(esk7_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_94,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_39]),c_0_40])])).

fof(c_0_95,plain,(
    ! [X42] :
      ( v2_struct_0(X42)
      | ~ l1_struct_0(X42)
      | ~ v1_xboole_0(u1_struct_0(X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_44]),c_0_40])])).

cnf(c_0_97,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_49]),c_0_40])])).

cnf(c_0_99,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_40])]),c_0_99]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.20/0.39  # and selection function SelectCQIPrecWNTNp.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.029 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t59_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tmap_1)).
% 0.20/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.39  fof(d9_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_2)).
% 0.20/0.39  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 0.20/0.39  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.20/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.39  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.20/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.20/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.39  fof(t72_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,X2)=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 0.20/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.39  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.20/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.39  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)))))))), inference(assume_negation,[status(cth)],[t59_tmap_1])).
% 0.20/0.39  fof(c_0_17, plain, ![X39]:(~l1_pre_topc(X39)|l1_struct_0(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.39  fof(c_0_18, negated_conjecture, ![X58]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk4_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))))&((~m1_subset_1(X58,u1_struct_0(esk4_0))|(~r2_hidden(X58,u1_struct_0(esk5_0))|k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,X58)=k1_funct_1(esk7_0,X58)))&~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).
% 0.20/0.39  fof(c_0_19, plain, ![X40, X41]:(~l1_pre_topc(X40)|(~m1_pre_topc(X41,X40)|l1_pre_topc(X41))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.39  fof(c_0_20, plain, ![X25, X26, X27, X28, X29]:((~r2_funct_2(X25,X26,X27,X28)|(~m1_subset_1(X29,X25)|k1_funct_1(X27,X29)=k1_funct_1(X28,X29))|(~v1_funct_1(X28)|~v1_funct_2(X28,X25,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))|(~v1_funct_1(X27)|~v1_funct_2(X27,X25,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))&((m1_subset_1(esk2_4(X25,X26,X27,X28),X25)|r2_funct_2(X25,X26,X27,X28)|(~v1_funct_1(X28)|~v1_funct_2(X28,X25,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))|(~v1_funct_1(X27)|~v1_funct_2(X27,X25,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))&(k1_funct_1(X27,esk2_4(X25,X26,X27,X28))!=k1_funct_1(X28,esk2_4(X25,X26,X27,X28))|r2_funct_2(X25,X26,X27,X28)|(~v1_funct_1(X28)|~v1_funct_2(X28,X25,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))|(~v1_funct_1(X27)|~v1_funct_2(X27,X25,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).
% 0.20/0.39  fof(c_0_21, plain, ![X47, X48, X49, X50]:(((v1_funct_1(k2_tmap_1(X47,X48,X49,X50))|(~l1_struct_0(X47)|~l1_struct_0(X48)|~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))|~l1_struct_0(X50)))&(v1_funct_2(k2_tmap_1(X47,X48,X49,X50),u1_struct_0(X50),u1_struct_0(X48))|(~l1_struct_0(X47)|~l1_struct_0(X48)|~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))|~l1_struct_0(X50))))&(m1_subset_1(k2_tmap_1(X47,X48,X49,X50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X48))))|(~l1_struct_0(X47)|~l1_struct_0(X48)|~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))|~l1_struct_0(X50)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 0.20/0.39  cnf(c_0_22, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_25, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_27, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),X1)|r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_28, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_31, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_24])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_24])])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),X1,esk7_0)|m1_subset_1(esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),X1,esk7_0),u1_struct_0(esk5_0))|~v1_funct_2(X1,u1_struct_0(esk5_0),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (v1_funct_2(k2_tmap_1(esk4_0,esk3_0,esk6_0,X1),u1_struct_0(X1),u1_struct_0(esk3_0))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_22, c_0_37])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_42, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0),u1_struct_0(esk5_0))|~v1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0))|~m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])]), c_0_41])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (v1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,X1))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])])).
% 0.20/0.39  cnf(c_0_45, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  fof(c_0_46, plain, ![X43, X44, X45, X46]:(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|(~v1_funct_1(X45)|~v1_funct_2(X45,u1_struct_0(X43),u1_struct_0(X44))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X44))))|(~m1_pre_topc(X46,X43)|k2_tmap_1(X43,X44,X45,X46)=k2_partfun1(u1_struct_0(X43),u1_struct_0(X44),X45,u1_struct_0(X46)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.20/0.39  fof(c_0_47, plain, ![X11, X12]:(~m1_subset_1(X11,X12)|(v1_xboole_0(X12)|r2_hidden(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0),u1_struct_0(esk5_0))|~m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_40])])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])])).
% 0.20/0.39  cnf(c_0_50, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  fof(c_0_53, plain, ![X31, X32, X33, X34]:(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k2_partfun1(X31,X32,X33,X34)=k7_relat_1(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.20/0.39  fof(c_0_54, plain, ![X13, X14, X15]:(~r2_hidden(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X15))|m1_subset_1(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.39  cnf(c_0_55, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_40])])).
% 0.20/0.39  fof(c_0_57, plain, ![X51, X52]:(~l1_pre_topc(X51)|(~m1_pre_topc(X52,X51)|m1_subset_1(u1_struct_0(X52),k1_zfmisc_1(u1_struct_0(X51))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.20/0.39  fof(c_0_58, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|~v1_xboole_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.39  fof(c_0_59, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.39  fof(c_0_60, plain, ![X19, X20, X21]:(~v1_relat_1(X21)|~v1_funct_1(X21)|(~r2_hidden(X19,X20)|k1_funct_1(k7_relat_1(X21,X20),X19)=k1_funct_1(X21,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(X1),X2,u1_struct_0(esk5_0))=k2_tmap_1(esk4_0,X1,X2,esk5_0)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_26]), c_0_51]), c_0_24])]), c_0_52])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_64, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.39  fof(c_0_65, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|v1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.39  cnf(c_0_66, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.39  cnf(c_0_67, negated_conjecture, (r2_hidden(esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0),u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.39  cnf(c_0_68, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.39  fof(c_0_69, plain, ![X35, X36, X37, X38]:(v1_xboole_0(X35)|~v1_funct_1(X37)|~v1_funct_2(X37,X35,X36)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~m1_subset_1(X38,X35)|k3_funct_2(X35,X36,X37,X38)=k1_funct_1(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.20/0.39  cnf(c_0_70, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.39  cnf(c_0_71, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.39  cnf(c_0_72, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0))=k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_32]), c_0_62]), c_0_23]), c_0_35]), c_0_36])]), c_0_63])).
% 0.20/0.39  cnf(c_0_74, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,X1)=k7_relat_1(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_36]), c_0_35])])).
% 0.20/0.39  cnf(c_0_75, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.39  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0),X1)|v1_xboole_0(u1_struct_0(esk5_0))|~m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.39  cnf(c_0_77, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_26]), c_0_24])])).
% 0.20/0.39  cnf(c_0_78, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.39  cnf(c_0_79, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.39  cnf(c_0_80, negated_conjecture, (k1_funct_1(k7_relat_1(X1,u1_struct_0(esk5_0)),esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))=k1_funct_1(X1,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))|v1_xboole_0(u1_struct_0(esk5_0))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_72, c_0_67])).
% 0.20/0.39  cnf(c_0_81, negated_conjecture, (k7_relat_1(esk6_0,u1_struct_0(esk5_0))=k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.39  cnf(c_0_82, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_75, c_0_36])).
% 0.20/0.39  cnf(c_0_83, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,X1)=k1_funct_1(esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.39  cnf(c_0_85, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,X1)=k1_funct_1(esk6_0,X1)|v1_xboole_0(u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_32]), c_0_35]), c_0_36])])).
% 0.20/0.39  cnf(c_0_86, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_79, c_0_77])).
% 0.20/0.39  cnf(c_0_87, plain, (r2_funct_2(X2,X3,X1,X4)|k1_funct_1(X1,esk2_4(X2,X3,X1,X4))!=k1_funct_1(X4,esk2_4(X2,X3,X1,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_88, negated_conjecture, (k1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))=k1_funct_1(esk6_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_35]), c_0_82])])).
% 0.20/0.39  cnf(c_0_89, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))=k1_funct_1(esk7_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_67]), c_0_84])).
% 0.20/0.39  cnf(c_0_90, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))=k1_funct_1(esk6_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_84]), c_0_86])).
% 0.20/0.39  cnf(c_0_91, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|k1_funct_1(esk6_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))!=k1_funct_1(esk7_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))|~v1_funct_2(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk3_0))|~v1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0))|~m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_28]), c_0_29]), c_0_30])]), c_0_41])).
% 0.20/0.39  cnf(c_0_92, negated_conjecture, (k1_funct_1(esk6_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))=k1_funct_1(esk7_0,esk2_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.20/0.39  cnf(c_0_93, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|~v1_funct_2(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk3_0))|~v1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0))|~m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.20/0.39  cnf(c_0_94, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|~v1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0))|~m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_39]), c_0_40])])).
% 0.20/0.39  fof(c_0_95, plain, ![X42]:(v2_struct_0(X42)|~l1_struct_0(X42)|~v1_xboole_0(u1_struct_0(X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.39  cnf(c_0_96, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|~m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_44]), c_0_40])])).
% 0.20/0.39  cnf(c_0_97, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.20/0.39  cnf(c_0_98, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_49]), c_0_40])])).
% 0.20/0.39  cnf(c_0_99, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_40])]), c_0_99]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 101
% 0.20/0.39  # Proof object clause steps            : 68
% 0.20/0.39  # Proof object formula steps           : 33
% 0.20/0.39  # Proof object conjectures             : 52
% 0.20/0.39  # Proof object clause conjectures      : 49
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 34
% 0.20/0.39  # Proof object initial formulas used   : 16
% 0.20/0.39  # Proof object generating inferences   : 33
% 0.20/0.39  # Proof object simplifying inferences  : 64
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 16
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 36
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 36
% 0.20/0.39  # Processed clauses                    : 180
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 10
% 0.20/0.39  # ...remaining for further processing  : 170
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 11
% 0.20/0.39  # Backward-rewritten                   : 28
% 0.20/0.39  # Generated clauses                    : 144
% 0.20/0.39  # ...of the previous two non-trivial   : 136
% 0.20/0.39  # Contextual simplify-reflections      : 9
% 0.20/0.39  # Paramodulations                      : 143
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 1
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 95
% 0.20/0.39  #    Positive orientable unit clauses  : 27
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 4
% 0.20/0.39  #    Non-unit-clauses                  : 64
% 0.20/0.39  # Current number of unprocessed clauses: 28
% 0.20/0.39  # ...number of literals in the above   : 114
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 75
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 2294
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 714
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 30
% 0.20/0.39  # Unit Clause-clause subsumption calls : 41
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 11
% 0.20/0.39  # BW rewrite match successes           : 5
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 8980
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.044 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.048 s
% 0.20/0.39  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
