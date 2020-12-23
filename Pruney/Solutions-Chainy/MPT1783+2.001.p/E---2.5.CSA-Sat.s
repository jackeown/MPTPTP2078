%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:12 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 (1653 expanded)
%              Number of clauses        :   58 ( 552 expanded)
%              Number of leaves         :   10 ( 410 expanded)
%              Depth                    :    9
%              Number of atoms          :  530 (10917 expanded)
%              Number of equality atoms :   24 (  71 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   64 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( v1_funct_1(k4_tmap_1(X1,X2))
            & v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
            & v5_pre_topc(k4_tmap_1(X1,X2),X2,X1)
            & m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(d5_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(dt_k4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k4_tmap_1(X1,X2))
        & v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(t89_tmap_1,axiom,(
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
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & v5_pre_topc(X5,X3,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
                          & v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
                          & v5_pre_topc(k3_tmap_1(X1,X2,X3,X4,X5),X4,X2)
                          & m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(d7_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => k4_tmap_1(X1,X2) = k2_tmap_1(X1,X1,k3_struct_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tmap_1)).

fof(fc3_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_funct_1(k3_struct_0(X1))
        & v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))
        & v5_pre_topc(k3_struct_0(X1),X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ( v1_funct_1(k4_tmap_1(X1,X2))
              & v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
              & v5_pre_topc(k4_tmap_1(X1,X2),X2,X1)
              & m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t98_tmap_1])).

fof(c_0_11,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | m1_pre_topc(X21,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ( ~ v1_funct_1(k4_tmap_1(esk1_0,esk2_0))
      | ~ v1_funct_2(k4_tmap_1(esk1_0,esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
      | ~ v5_pre_topc(k4_tmap_1(esk1_0,esk2_0),esk2_0,esk1_0)
      | ~ m1_subset_1(k4_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(X13,X11)
      | ~ m1_pre_topc(X14,X11)
      | ~ v1_funct_1(X15)
      | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X12))
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X12))))
      | ~ m1_pre_topc(X14,X13)
      | k3_tmap_1(X11,X12,X13,X14,X15) = k2_partfun1(u1_struct_0(X13),u1_struct_0(X12),X15,u1_struct_0(X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_14,plain,(
    ! [X22,X23,X24] :
      ( ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | ~ m1_pre_topc(X24,X23)
      | m1_pre_topc(X24,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_15,plain,(
    ! [X18,X19] :
      ( ( v1_funct_1(k4_tmap_1(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) )
      & ( v1_funct_2(k4_tmap_1(X18,X19),u1_struct_0(X19),u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) )
      & ( m1_subset_1(k4_tmap_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X18))))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).

cnf(c_0_16,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_20,plain,
    ( m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_24,plain,
    ( v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_25,plain,
    ( v1_funct_1(k4_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_26,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_18,c_0_19]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk1_0,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk1_0,esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(k4_tmap_1(esk1_0,esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_21]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( k3_tmap_1(X1,esk1_0,esk1_0,X2,k4_tmap_1(esk1_0,esk1_0)) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk1_0),u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

fof(c_0_32,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( ( v1_funct_1(k3_tmap_1(X25,X26,X27,X28,X29))
        | ~ m1_pre_topc(X28,X27)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))
        | ~ v5_pre_topc(X29,X27,X26)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v1_funct_2(k3_tmap_1(X25,X26,X27,X28,X29),u1_struct_0(X28),u1_struct_0(X26))
        | ~ m1_pre_topc(X28,X27)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))
        | ~ v5_pre_topc(X29,X27,X26)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v5_pre_topc(k3_tmap_1(X25,X26,X27,X28,X29),X28,X26)
        | ~ m1_pre_topc(X28,X27)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))
        | ~ v5_pre_topc(X29,X27,X26)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(k3_tmap_1(X25,X26,X27,X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26))))
        | ~ m1_pre_topc(X28,X27)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))
        | ~ v5_pre_topc(X29,X27,X26)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t89_tmap_1])])])])])).

cnf(c_0_33,negated_conjecture,
    ( k3_tmap_1(X1,esk1_0,esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0)) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk1_0),u1_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( k3_tmap_1(X1,esk1_0,esk1_0,esk2_0,k4_tmap_1(esk1_0,esk1_0)) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk1_0),u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X4,X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X4,X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( v5_pre_topc(k3_tmap_1(X1,X2,X3,X4,X5),X4,X2)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X4,X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X4,X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X7,X8,X9,X10] :
      ( v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(X8)
      | ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
      | ~ m1_pre_topc(X10,X7)
      | k2_tmap_1(X7,X8,X9,X10) = k2_partfun1(u1_struct_0(X7),u1_struct_0(X8),X9,u1_struct_0(X10)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_funct_1(k4_tmap_1(esk1_0,esk2_0))
    | ~ v1_funct_2(k4_tmap_1(esk1_0,esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    | ~ v5_pre_topc(k4_tmap_1(esk1_0,esk2_0),esk2_0,esk1_0)
    | ~ m1_subset_1(k4_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(k4_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_31]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

fof(c_0_42,plain,(
    ! [X16,X17] :
      ( v2_struct_0(X16)
      | ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | ~ m1_pre_topc(X17,X16)
      | k4_tmap_1(X16,X17) = k2_tmap_1(X16,X16,k3_struct_0(X16),X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_tmap_1])])])])).

fof(c_0_43,plain,(
    ! [X20] :
      ( ( v1_funct_1(k3_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( v1_funct_2(k3_struct_0(X20),u1_struct_0(X20),u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( v5_pre_topc(k3_struct_0(X20),X20,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_tmap_1])])])])).

cnf(c_0_44,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk1_0),u1_struct_0(esk1_0)) = k3_tmap_1(esk1_0,esk1_0,esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_21]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk1_0),u1_struct_0(esk2_0)) = k3_tmap_1(esk1_0,esk1_0,esk1_0,esk2_0,k4_tmap_1(esk1_0,esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_21]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_46,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v5_pre_topc(X5,X3,X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_35,c_0_19]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_31]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk1_0,esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_31]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_49,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v5_pre_topc(X5,X3,X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_36,c_0_19]),
    [final]).

cnf(c_0_50,plain,
    ( v5_pre_topc(k3_tmap_1(X1,X2,X3,X4,X5),X4,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v5_pre_topc(X5,X3,X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_37,c_0_19]),
    [final]).

cnf(c_0_51,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v5_pre_topc(X5,X3,X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_38,c_0_19]),
    [final]).

cnf(c_0_52,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_39]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

fof(c_0_54,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(X6)
      | l1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_55,negated_conjecture,
    ( ~ v5_pre_topc(k4_tmap_1(esk1_0,esk2_0),esk2_0,esk1_0)
    | ~ m1_subset_1(k4_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | ~ v1_funct_2(k4_tmap_1(esk1_0,esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | k4_tmap_1(X1,X2) = k2_tmap_1(X1,X1,k3_struct_0(X1),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42]),
    [final]).

cnf(c_0_57,plain,
    ( v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_58,plain,
    ( v5_pre_topc(k3_struct_0(X1),X1,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_59,plain,
    ( v1_funct_1(k3_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( k3_tmap_1(X1,esk1_0,esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0)) = k3_tmap_1(esk1_0,esk1_0,esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_33,c_0_44]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( k3_tmap_1(X1,esk1_0,esk1_0,esk2_0,k4_tmap_1(esk1_0,esk1_0)) = k3_tmap_1(esk1_0,esk1_0,esk1_0,esk2_0,k4_tmap_1(esk1_0,esk1_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_34,c_0_45]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(X1,esk1_0,esk1_0,X2,k4_tmap_1(esk1_0,esk1_0)),u1_struct_0(X2),u1_struct_0(esk1_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k4_tmap_1(esk1_0,esk1_0),esk1_0,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_27]),c_0_28]),c_0_29]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( k3_tmap_1(X1,esk1_0,esk2_0,X2,k4_tmap_1(esk1_0,esk2_0)) = k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk2_0),u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk2_0)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_47]),c_0_48]),c_0_41]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(X1,esk1_0,esk1_0,X2,k4_tmap_1(esk1_0,esk1_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk1_0))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k4_tmap_1(esk1_0,esk1_0),esk1_0,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_27]),c_0_28]),c_0_29]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(X1,esk1_0,esk1_0,X2,k4_tmap_1(esk1_0,esk1_0)),X2,esk1_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k4_tmap_1(esk1_0,esk1_0),esk1_0,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_27]),c_0_28]),c_0_29]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(X1,esk1_0,esk1_0,X2,k4_tmap_1(esk1_0,esk1_0)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k4_tmap_1(esk1_0,esk1_0),esk1_0,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_27]),c_0_28]),c_0_29]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk2_0),u1_struct_0(X1)) = k2_tmap_1(esk2_0,esk1_0,k4_tmap_1(esk1_0,esk2_0),X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ v2_pre_topc(esk2_0)
    | ~ l1_pre_topc(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_47]),c_0_48]),c_0_41]),c_0_22]),c_0_17])]),c_0_23]),c_0_53]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk1_0),u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_27]),c_0_28]),c_0_29]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_31]),
    [final]).

cnf(c_0_70,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( ~ v5_pre_topc(k4_tmap_1(esk1_0,esk2_0),esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_48])]),c_0_47])]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0),esk1_0) = k3_tmap_1(esk1_0,esk1_0,esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_44]),c_0_21]),c_0_27]),c_0_28]),c_0_29]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0),esk2_0) = k3_tmap_1(esk1_0,esk1_0,esk1_0,esk2_0,k4_tmap_1(esk1_0,esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_45]),c_0_31]),c_0_27]),c_0_28]),c_0_29]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk1_0,k3_struct_0(esk1_0),esk1_0) = k4_tmap_1(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_21]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk1_0,k3_struct_0(esk1_0),esk2_0) = k4_tmap_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_31]),c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( v1_funct_2(k3_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( v5_pre_topc(k3_struct_0(esk1_0),esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_22]),c_0_17])]),c_0_23]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_1(k3_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_22]),c_0_17])]),c_0_23]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:31:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05AN
% 0.13/0.39  # and selection function PSelectComplexExceptUniqMaxPosHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.030 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # No proof found!
% 0.13/0.39  # SZS status CounterSatisfiable
% 0.13/0.39  # SZS output start Saturation
% 0.13/0.39  fof(t98_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(((v1_funct_1(k4_tmap_1(X1,X2))&v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&v5_pre_topc(k4_tmap_1(X1,X2),X2,X1))&m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_tmap_1)).
% 0.13/0.39  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.13/0.39  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.13/0.39  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.13/0.39  fof(dt_k4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k4_tmap_1(X1,X2))&v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 0.13/0.39  fof(t89_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>(((v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))&v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,X3,X4,X5),X4,X2))&m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_tmap_1)).
% 0.13/0.39  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.13/0.39  fof(d7_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>k4_tmap_1(X1,X2)=k2_tmap_1(X1,X1,k3_struct_0(X1),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tmap_1)).
% 0.13/0.39  fof(fc3_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>((v1_funct_1(k3_struct_0(X1))&v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1)))&v5_pre_topc(k3_struct_0(X1),X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_tmap_1)).
% 0.13/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(((v1_funct_1(k4_tmap_1(X1,X2))&v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&v5_pre_topc(k4_tmap_1(X1,X2),X2,X1))&m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))))), inference(assume_negation,[status(cth)],[t98_tmap_1])).
% 0.13/0.39  fof(c_0_11, plain, ![X21]:(~l1_pre_topc(X21)|m1_pre_topc(X21,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.13/0.39  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&(~v1_funct_1(k4_tmap_1(esk1_0,esk2_0))|~v1_funct_2(k4_tmap_1(esk1_0,esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~v5_pre_topc(k4_tmap_1(esk1_0,esk2_0),esk2_0,esk1_0)|~m1_subset_1(k4_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.13/0.39  fof(c_0_13, plain, ![X11, X12, X13, X14, X15]:(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|(~m1_pre_topc(X13,X11)|(~m1_pre_topc(X14,X11)|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X12))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X12))))|(~m1_pre_topc(X14,X13)|k3_tmap_1(X11,X12,X13,X14,X15)=k2_partfun1(u1_struct_0(X13),u1_struct_0(X12),X15,u1_struct_0(X14)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.13/0.39  fof(c_0_14, plain, ![X22, X23, X24]:(~v2_pre_topc(X22)|~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|(~m1_pre_topc(X24,X23)|m1_pre_topc(X24,X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.13/0.39  fof(c_0_15, plain, ![X18, X19]:(((v1_funct_1(k4_tmap_1(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18)))&(v1_funct_2(k4_tmap_1(X18,X19),u1_struct_0(X19),u1_struct_0(X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18))))&(m1_subset_1(k4_tmap_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X18))))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).
% 0.13/0.39  cnf(c_0_16, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.39  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.39  cnf(c_0_18, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_19, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.13/0.39  cnf(c_0_20, plain, (m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_16, c_0_17]), ['final']).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.39  cnf(c_0_24, plain, (v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.39  cnf(c_0_25, plain, (v1_funct_1(k4_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.39  cnf(c_0_26, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_18, c_0_19]), ['final']).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (m1_subset_1(k4_tmap_1(esk1_0,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (v1_funct_2(k4_tmap_1(esk1_0,esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_21]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (v1_funct_1(k4_tmap_1(esk1_0,esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_21]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (k3_tmap_1(X1,esk1_0,esk1_0,X2,k4_tmap_1(esk1_0,esk1_0))=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk1_0),u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.39  fof(c_0_32, plain, ![X25, X26, X27, X28, X29]:((((v1_funct_1(k3_tmap_1(X25,X26,X27,X28,X29))|~m1_pre_topc(X28,X27)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))|~v5_pre_topc(X29,X27,X26)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26)))))|(v2_struct_0(X28)|~m1_pre_topc(X28,X25))|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(v1_funct_2(k3_tmap_1(X25,X26,X27,X28,X29),u1_struct_0(X28),u1_struct_0(X26))|~m1_pre_topc(X28,X27)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))|~v5_pre_topc(X29,X27,X26)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26)))))|(v2_struct_0(X28)|~m1_pre_topc(X28,X25))|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(v5_pre_topc(k3_tmap_1(X25,X26,X27,X28,X29),X28,X26)|~m1_pre_topc(X28,X27)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))|~v5_pre_topc(X29,X27,X26)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26)))))|(v2_struct_0(X28)|~m1_pre_topc(X28,X25))|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(m1_subset_1(k3_tmap_1(X25,X26,X27,X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26))))|~m1_pre_topc(X28,X27)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))|~v5_pre_topc(X29,X27,X26)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26)))))|(v2_struct_0(X28)|~m1_pre_topc(X28,X25))|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t89_tmap_1])])])])])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (k3_tmap_1(X1,esk1_0,esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0))=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk1_0),u1_struct_0(esk1_0))|v2_struct_0(X1)|~m1_pre_topc(esk1_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_30, c_0_21])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (k3_tmap_1(X1,esk1_0,esk1_0,esk2_0,k4_tmap_1(esk1_0,esk1_0))=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk1_0),u1_struct_0(esk2_0))|v2_struct_0(X1)|~m1_pre_topc(esk1_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.39  cnf(c_0_35, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X4,X3)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v5_pre_topc(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_36, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X4,X3)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v5_pre_topc(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_37, plain, (v5_pre_topc(k3_tmap_1(X1,X2,X3,X4,X5),X4,X2)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X4,X3)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v5_pre_topc(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_38, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X4,X3)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v5_pre_topc(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  fof(c_0_39, plain, ![X7, X8, X9, X10]:(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)|(~v1_funct_1(X9)|~v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))|(~m1_pre_topc(X10,X7)|k2_tmap_1(X7,X8,X9,X10)=k2_partfun1(u1_struct_0(X7),u1_struct_0(X8),X9,u1_struct_0(X10)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (~v1_funct_1(k4_tmap_1(esk1_0,esk2_0))|~v1_funct_2(k4_tmap_1(esk1_0,esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~v5_pre_topc(k4_tmap_1(esk1_0,esk2_0),esk2_0,esk1_0)|~m1_subset_1(k4_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (v1_funct_1(k4_tmap_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_31]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  fof(c_0_42, plain, ![X16, X17]:(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|(~m1_pre_topc(X17,X16)|k4_tmap_1(X16,X17)=k2_tmap_1(X16,X16,k3_struct_0(X16),X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_tmap_1])])])])).
% 0.20/0.39  fof(c_0_43, plain, ![X20]:(((v1_funct_1(k3_struct_0(X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(v1_funct_2(k3_struct_0(X20),u1_struct_0(X20),u1_struct_0(X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))))&(v5_pre_topc(k3_struct_0(X20),X20,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_tmap_1])])])])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk1_0),u1_struct_0(esk1_0))=k3_tmap_1(esk1_0,esk1_0,esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_21]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk1_0),u1_struct_0(esk2_0))=k3_tmap_1(esk1_0,esk1_0,esk1_0,esk2_0,k4_tmap_1(esk1_0,esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_21]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_46, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v5_pre_topc(X5,X3,X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_35, c_0_19]), ['final']).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (m1_subset_1(k4_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_31]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (v1_funct_2(k4_tmap_1(esk1_0,esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_31]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_49, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v5_pre_topc(X5,X3,X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_36, c_0_19]), ['final']).
% 0.20/0.39  cnf(c_0_50, plain, (v5_pre_topc(k3_tmap_1(X1,X2,X3,X4,X5),X4,X2)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v5_pre_topc(X5,X3,X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_37, c_0_19]), ['final']).
% 0.20/0.39  cnf(c_0_51, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v5_pre_topc(X5,X3,X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_38, c_0_19]), ['final']).
% 0.20/0.39  cnf(c_0_52, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_39]), ['final']).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.20/0.39  fof(c_0_54, plain, ![X6]:(~l1_pre_topc(X6)|l1_struct_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (~v5_pre_topc(k4_tmap_1(esk1_0,esk2_0),esk2_0,esk1_0)|~m1_subset_1(k4_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|~v1_funct_2(k4_tmap_1(esk1_0,esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])])).
% 0.20/0.39  cnf(c_0_56, plain, (v2_struct_0(X1)|k4_tmap_1(X1,X2)=k2_tmap_1(X1,X1,k3_struct_0(X1),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42]), ['final']).
% 0.20/0.39  cnf(c_0_57, plain, (v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.20/0.39  cnf(c_0_58, plain, (v5_pre_topc(k3_struct_0(X1),X1,X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.20/0.39  cnf(c_0_59, plain, (v1_funct_1(k3_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (k3_tmap_1(X1,esk1_0,esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0))=k3_tmap_1(esk1_0,esk1_0,esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0))|v2_struct_0(X1)|~m1_pre_topc(esk1_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[c_0_33, c_0_44]), ['final']).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (k3_tmap_1(X1,esk1_0,esk1_0,esk2_0,k4_tmap_1(esk1_0,esk1_0))=k3_tmap_1(esk1_0,esk1_0,esk1_0,esk2_0,k4_tmap_1(esk1_0,esk1_0))|v2_struct_0(X1)|~m1_pre_topc(esk1_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[c_0_34, c_0_45]), ['final']).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (v1_funct_2(k3_tmap_1(X1,esk1_0,esk1_0,X2,k4_tmap_1(esk1_0,esk1_0)),u1_struct_0(X2),u1_struct_0(esk1_0))|v2_struct_0(X1)|v2_struct_0(X2)|~v5_pre_topc(k4_tmap_1(esk1_0,esk1_0),esk1_0,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_27]), c_0_28]), c_0_29]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (k3_tmap_1(X1,esk1_0,esk2_0,X2,k4_tmap_1(esk1_0,esk2_0))=k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk2_0),u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk2_0)|~m1_pre_topc(esk2_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_47]), c_0_48]), c_0_41]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, (m1_subset_1(k3_tmap_1(X1,esk1_0,esk1_0,X2,k4_tmap_1(esk1_0,esk1_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk1_0))))|v2_struct_0(X1)|v2_struct_0(X2)|~v5_pre_topc(k4_tmap_1(esk1_0,esk1_0),esk1_0,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_27]), c_0_28]), c_0_29]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (v5_pre_topc(k3_tmap_1(X1,esk1_0,esk1_0,X2,k4_tmap_1(esk1_0,esk1_0)),X2,esk1_0)|v2_struct_0(X1)|v2_struct_0(X2)|~v5_pre_topc(k4_tmap_1(esk1_0,esk1_0),esk1_0,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_27]), c_0_28]), c_0_29]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (v1_funct_1(k3_tmap_1(X1,esk1_0,esk1_0,X2,k4_tmap_1(esk1_0,esk1_0)))|v2_struct_0(X1)|v2_struct_0(X2)|~v5_pre_topc(k4_tmap_1(esk1_0,esk1_0),esk1_0,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_27]), c_0_28]), c_0_29]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_67, negated_conjecture, (k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk2_0),u1_struct_0(X1))=k2_tmap_1(esk2_0,esk1_0,k4_tmap_1(esk1_0,esk2_0),X1)|~m1_pre_topc(X1,esk2_0)|~v2_pre_topc(esk2_0)|~l1_pre_topc(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_47]), c_0_48]), c_0_41]), c_0_22]), c_0_17])]), c_0_23]), c_0_53]), ['final']).
% 0.20/0.39  cnf(c_0_68, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk1_0),u1_struct_0(X1))=k2_tmap_1(esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0),X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_27]), c_0_28]), c_0_29]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (m1_pre_topc(esk2_0,X1)|~m1_pre_topc(esk1_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_31]), ['final']).
% 0.20/0.39  cnf(c_0_70, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54]), ['final']).
% 0.20/0.39  cnf(c_0_71, negated_conjecture, (~v5_pre_topc(k4_tmap_1(esk1_0,esk2_0),esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_48])]), c_0_47])]), ['final']).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (k2_tmap_1(esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0),esk1_0)=k3_tmap_1(esk1_0,esk1_0,esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_44]), c_0_21]), c_0_27]), c_0_28]), c_0_29]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (k2_tmap_1(esk1_0,esk1_0,k4_tmap_1(esk1_0,esk1_0),esk2_0)=k3_tmap_1(esk1_0,esk1_0,esk1_0,esk2_0,k4_tmap_1(esk1_0,esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_45]), c_0_31]), c_0_27]), c_0_28]), c_0_29]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_74, negated_conjecture, (k2_tmap_1(esk1_0,esk1_0,k3_struct_0(esk1_0),esk1_0)=k4_tmap_1(esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_21]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_75, negated_conjecture, (k2_tmap_1(esk1_0,esk1_0,k3_struct_0(esk1_0),esk2_0)=k4_tmap_1(esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_31]), c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_76, negated_conjecture, (v1_funct_2(k3_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_77, negated_conjecture, (v5_pre_topc(k3_struct_0(esk1_0),esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  cnf(c_0_78, negated_conjecture, (v1_funct_1(k3_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_22]), c_0_17])]), c_0_23]), ['final']).
% 0.20/0.39  # SZS output end Saturation
% 0.20/0.39  # Proof object total steps             : 79
% 0.20/0.39  # Proof object clause steps            : 58
% 0.20/0.39  # Proof object formula steps           : 21
% 0.20/0.39  # Proof object conjectures             : 40
% 0.20/0.39  # Proof object clause conjectures      : 37
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 22
% 0.20/0.39  # Proof object initial formulas used   : 10
% 0.20/0.39  # Proof object generating inferences   : 27
% 0.20/0.39  # Proof object simplifying inferences  : 127
% 0.20/0.39  # Parsed axioms                        : 10
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 22
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 22
% 0.20/0.39  # Processed clauses                    : 85
% 0.20/0.39  # ...of these trivial                  : 2
% 0.20/0.39  # ...subsumed                          : 8
% 0.20/0.39  # ...remaining for further processing  : 75
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 4
% 0.20/0.39  # Generated clauses                    : 39
% 0.20/0.39  # ...of the previous two non-trivial   : 41
% 0.20/0.39  # Contextual simplify-reflections      : 5
% 0.20/0.39  # Paramodulations                      : 39
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
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
% 0.20/0.39  # Current number of processed clauses  : 49
% 0.20/0.39  #    Positive orientable unit clauses  : 19
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 3
% 0.20/0.39  #    Non-unit-clauses                  : 27
% 0.20/0.39  # Current number of unprocessed clauses: 0
% 0.20/0.39  # ...number of literals in the above   : 0
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 26
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 2316
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 48
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 9
% 0.20/0.39  # Unit Clause-clause subsumption calls : 0
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 17
% 0.20/0.39  # BW rewrite match successes           : 4
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 6000
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.037 s
% 0.20/0.39  # System time              : 0.007 s
% 0.20/0.39  # Total time               : 0.043 s
% 0.20/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
