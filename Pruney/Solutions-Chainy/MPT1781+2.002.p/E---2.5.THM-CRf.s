%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:09 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  109 (1992 expanded)
%              Number of clauses        :   74 ( 654 expanded)
%              Number of leaves         :   17 ( 486 expanded)
%              Depth                    :   19
%              Number of atoms          :  620 (16711 expanded)
%              Number of equality atoms :   51 (1276 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   48 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t96_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,u1_struct_0(X2))
                     => X4 = k1_funct_1(X3,X4) ) )
               => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t59_tmap_1,axiom,(
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

fof(dt_k4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k4_tmap_1(X1,X2))
        & v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

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

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(t95_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,u1_struct_0(X2))
               => k1_funct_1(k4_tmap_1(X1,X2),X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

fof(t173_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X4,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                     => ( ! [X6] :
                            ( m1_subset_1(X6,X1)
                           => ( r2_hidden(X6,X4)
                             => k3_funct_2(X1,X2,X3,X6) = k1_funct_1(X5,X6) ) )
                       => k2_partfun1(X1,X2,X3,X4) = X5 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_17,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_18,plain,(
    ! [X44,X45,X46] :
      ( ( ~ r1_tarski(u1_struct_0(X45),u1_struct_0(X46))
        | m1_pre_topc(X45,X46)
        | ~ m1_pre_topc(X46,X44)
        | ~ m1_pre_topc(X45,X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( ~ m1_pre_topc(X45,X46)
        | r1_tarski(u1_struct_0(X45),u1_struct_0(X46))
        | ~ m1_pre_topc(X46,X44)
        | ~ m1_pre_topc(X45,X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_hidden(X4,u1_struct_0(X2))
                       => X4 = k1_funct_1(X3,X4) ) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t96_tmap_1])).

cnf(c_0_21,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,(
    ! [X59] :
      ( ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & l1_pre_topc(esk4_0)
      & ~ v2_struct_0(esk5_0)
      & m1_pre_topc(esk5_0,esk4_0)
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))
      & ( ~ m1_subset_1(X59,u1_struct_0(esk4_0))
        | ~ r2_hidden(X59,u1_struct_0(esk5_0))
        | X59 = k1_funct_1(esk6_0,X59) )
      & ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k4_tmap_1(esk4_0,esk5_0),esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])])).

fof(c_0_24,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | l1_pre_topc(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_25,plain,(
    ! [X27,X28] :
      ( ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | ~ m1_pre_topc(X28,X27)
      | v2_pre_topc(X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_26,plain,(
    ! [X47,X48,X49,X50,X51] :
      ( ( m1_subset_1(esk3_5(X47,X48,X49,X50,X51),u1_struct_0(X48))
        | r2_funct_2(u1_struct_0(X49),u1_struct_0(X47),k2_tmap_1(X48,X47,X50,X49),X51)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X47))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X47))))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,u1_struct_0(X48),u1_struct_0(X47))
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X47))))
        | v2_struct_0(X49)
        | ~ m1_pre_topc(X49,X48)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48)
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) )
      & ( r2_hidden(esk3_5(X47,X48,X49,X50,X51),u1_struct_0(X49))
        | r2_funct_2(u1_struct_0(X49),u1_struct_0(X47),k2_tmap_1(X48,X47,X50,X49),X51)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X47))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X47))))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,u1_struct_0(X48),u1_struct_0(X47))
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X47))))
        | v2_struct_0(X49)
        | ~ m1_pre_topc(X49,X48)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48)
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) )
      & ( k3_funct_2(u1_struct_0(X48),u1_struct_0(X47),X50,esk3_5(X47,X48,X49,X50,X51)) != k1_funct_1(X51,esk3_5(X47,X48,X49,X50,X51))
        | r2_funct_2(u1_struct_0(X49),u1_struct_0(X47),k2_tmap_1(X48,X47,X50,X49),X51)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X47))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X47))))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,u1_struct_0(X48),u1_struct_0(X47))
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X47))))
        | v2_struct_0(X49)
        | ~ m1_pre_topc(X49,X48)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48)
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).

cnf(c_0_27,plain,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X40,X41] :
      ( ( v1_funct_1(k4_tmap_1(X40,X41))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | ~ m1_pre_topc(X41,X40) )
      & ( v1_funct_2(k4_tmap_1(X40,X41),u1_struct_0(X41),u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | ~ m1_pre_topc(X41,X40) )
      & ( m1_subset_1(k4_tmap_1(X40,X41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X40))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | ~ m1_pre_topc(X41,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).

fof(c_0_34,plain,(
    ! [X36,X37,X38,X39] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | v2_struct_0(X37)
      | ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | ~ v1_funct_1(X38)
      | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
      | ~ m1_pre_topc(X39,X36)
      | k2_tmap_1(X36,X37,X38,X39) = k2_partfun1(u1_struct_0(X36),u1_struct_0(X37),X38,u1_struct_0(X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_35,plain,
    ( r2_hidden(esk3_5(X1,X2,X3,X4,X5),u1_struct_0(X3))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_29])])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,plain,
    ( v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,plain,
    ( m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( v1_funct_1(k4_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk3_5(X1,X2,X3,X4,X5),u1_struct_0(X2))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_46,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(X1),k2_tmap_1(esk5_0,X1,X2,esk5_0),X3)
    | r2_hidden(esk3_5(X1,esk5_0,esk5_0,X2,X3),u1_struct_0(esk5_0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X3,u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk4_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_28]),c_0_29]),c_0_30])]),c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_28]),c_0_29]),c_0_30])]),c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(k4_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_28]),c_0_29]),c_0_30])]),c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( k2_tmap_1(esk5_0,X1,X2,esk5_0) = k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(X1),X2,u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_36]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_54,plain,(
    ! [X13,X14,X15,X16] :
      ( v1_xboole_0(X13)
      | ~ v1_funct_1(X15)
      | ~ v1_funct_2(X15,X13,X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | ~ m1_subset_1(X16,X13)
      | k3_funct_2(X13,X14,X15,X16) = k1_funct_1(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_55,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(X1),k2_tmap_1(esk5_0,X1,X2,esk5_0),X3)
    | m1_subset_1(esk3_5(X1,esk5_0,esk5_0,X2,X3),u1_struct_0(esk5_0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X3,u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_36]),c_0_37]),c_0_38])]),c_0_39])).

fof(c_0_56,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_57,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk5_0,esk4_0,X1,esk5_0),k4_tmap_1(esk4_0,esk5_0))
    | r2_hidden(esk3_5(esk4_0,esk5_0,esk5_0,X1,k4_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_29]),c_0_30]),c_0_48]),c_0_49])]),c_0_41])).

cnf(c_0_58,negated_conjecture,
    ( k2_tmap_1(esk5_0,esk4_0,esk6_0,esk5_0) = k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_29]),c_0_30]),c_0_52]),c_0_53])]),c_0_41])).

fof(c_0_59,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ l1_pre_topc(X33)
      | v2_struct_0(X34)
      | ~ m1_pre_topc(X34,X33)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | m1_subset_1(X35,u1_struct_0(X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_60,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk5_0,esk4_0,X1,esk5_0),k4_tmap_1(esk4_0,esk5_0))
    | m1_subset_1(esk3_5(esk4_0,esk5_0,esk5_0,X1,k4_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_47]),c_0_29]),c_0_30]),c_0_48]),c_0_49])]),c_0_41])).

cnf(c_0_62,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))
    | r2_hidden(esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_51]),c_0_58]),c_0_52]),c_0_53])])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_65,plain,(
    ! [X53,X54,X55] :
      ( v2_struct_0(X53)
      | ~ v2_pre_topc(X53)
      | ~ l1_pre_topc(X53)
      | v2_struct_0(X54)
      | ~ m1_pre_topc(X54,X53)
      | ~ m1_subset_1(X55,u1_struct_0(X53))
      | ~ r2_hidden(X55,u1_struct_0(X54))
      | k1_funct_1(k4_tmap_1(X53,X54),X55) = X55 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).

fof(c_0_66,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( m1_subset_1(esk2_5(X21,X22,X23,X24,X25),X21)
        | k2_partfun1(X21,X22,X23,X24) = X25
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X24,X22)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X24,X22)))
        | v1_xboole_0(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(X21))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | v1_xboole_0(X22)
        | v1_xboole_0(X21) )
      & ( r2_hidden(esk2_5(X21,X22,X23,X24,X25),X24)
        | k2_partfun1(X21,X22,X23,X24) = X25
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X24,X22)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X24,X22)))
        | v1_xboole_0(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(X21))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | v1_xboole_0(X22)
        | v1_xboole_0(X21) )
      & ( k3_funct_2(X21,X22,X23,esk2_5(X21,X22,X23,X24,X25)) != k1_funct_1(X25,esk2_5(X21,X22,X23,X24,X25))
        | k2_partfun1(X21,X22,X23,X24) = X25
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X24,X22)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X24,X22)))
        | v1_xboole_0(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(X21))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | v1_xboole_0(X22)
        | v1_xboole_0(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t173_funct_2])])])])])])).

fof(c_0_67,plain,(
    ! [X42,X43] :
      ( ~ l1_pre_topc(X42)
      | ~ m1_pre_topc(X43,X42)
      | m1_subset_1(u1_struct_0(X43),k1_zfmisc_1(u1_struct_0(X42))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_68,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,X1) = k1_funct_1(esk6_0,X1)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_51]),c_0_52]),c_0_53])])).

cnf(c_0_69,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))
    | m1_subset_1(esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_51]),c_0_58]),c_0_52]),c_0_53])])).

cnf(c_0_70,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( X1 = k1_funct_1(esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_28]),c_0_29])]),c_0_39]),c_0_41])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_funct_1(k4_tmap_1(X1,X2),X3) = X3
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X1)
    | k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_75,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,plain,
    ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X3,X4),X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_5(X2,X1,X4,X3,X5)) != k1_funct_1(X5,esk3_5(X2,X1,X4,X3,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_77,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0))) = k1_funct_1(esk6_0,esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)))
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( k1_funct_1(esk6_0,esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0))) = esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0))
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))
    | ~ m1_subset_1(esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_63])).

cnf(c_0_79,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))
    | m1_subset_1(esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_69])).

cnf(c_0_80,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(X1,esk5_0),esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0))) = esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0))
    | v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)),u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_63]),c_0_39])).

cnf(c_0_81,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk4_0),X2,u1_struct_0(esk5_0)) = esk6_0
    | m1_subset_1(esk2_5(X1,u1_struct_0(esk4_0),X2,u1_struct_0(esk5_0),esk6_0),X1)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk4_0))))
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(X1))
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk4_0))
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_51]),c_0_52]),c_0_53])])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_36]),c_0_37])])).

fof(c_0_83,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r2_funct_2(X17,X18,X19,X20)
        | X19 = X20
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,X17,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( X19 != X20
        | r2_funct_2(X17,X18,X19,X20)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,X17,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_84,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))
    | k1_funct_1(esk6_0,esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0))) != k1_funct_1(k4_tmap_1(esk4_0,esk5_0),esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_58]),c_0_36]),c_0_29]),c_0_37]),c_0_30]),c_0_38]),c_0_48]),c_0_52]),c_0_47]),c_0_51]),c_0_49]),c_0_53])]),c_0_39]),c_0_41])).

cnf(c_0_85,negated_conjecture,
    ( k1_funct_1(esk6_0,esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0))) = esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0))
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk4_0,esk5_0),esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0))) = esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0))
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_28]),c_0_29]),c_0_30])]),c_0_41]),c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)) = esk6_0
    | m1_subset_1(esk2_5(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_51]),c_0_52]),c_0_82]),c_0_53])])).

cnf(c_0_88,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_89,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])).

cnf(c_0_91,plain,
    ( k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X3,esk2_5(X1,X2,X3,X4,X5)) != k1_funct_1(X5,esk2_5(X1,X2,X3,X4,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_92,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,esk2_5(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0),esk6_0)) = k1_funct_1(esk6_0,esk2_5(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0),esk6_0))
    | k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)) = esk6_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_87])).

cnf(c_0_93,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)) = k4_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))
    | ~ v1_funct_2(k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    | ~ v1_funct_1(k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_48]),c_0_47]),c_0_49])])).

cnf(c_0_95,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)) = esk6_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_52]),c_0_82]),c_0_51]),c_0_53])])).

cnf(c_0_96,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k4_tmap_1(esk4_0,esk5_0),k4_tmap_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k4_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_47]),c_0_49])])).

fof(c_0_97,plain,(
    ! [X32] :
      ( v2_struct_0(X32)
      | ~ l1_struct_0(X32)
      | ~ v1_xboole_0(u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_98,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k4_tmap_1(esk4_0,esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_99,negated_conjecture,
    ( esk6_0 = k4_tmap_1(esk4_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_52]),c_0_51]),c_0_53])])).

cnf(c_0_100,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k4_tmap_1(esk4_0,esk5_0),k4_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_48])])).

cnf(c_0_101,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100])])).

fof(c_0_103,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_104,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_39])).

cnf(c_0_105,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_37])])).

cnf(c_0_107,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_106]),c_0_41])).

cnf(c_0_108,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_105]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:50:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.41  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.030 s
% 0.13/0.41  # Presaturation interreduction done
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.41  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.13/0.41  fof(t96_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 0.13/0.41  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.41  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.13/0.41  fof(t59_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tmap_1)).
% 0.13/0.41  fof(dt_k4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k4_tmap_1(X1,X2))&v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 0.13/0.41  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.13/0.41  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.13/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.41  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.13/0.41  fof(t95_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,u1_struct_0(X2))=>k1_funct_1(k4_tmap_1(X1,X2),X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 0.13/0.41  fof(t173_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X4,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(![X6]:(m1_subset_1(X6,X1)=>(r2_hidden(X6,X4)=>k3_funct_2(X1,X2,X3,X6)=k1_funct_1(X5,X6)))=>k2_partfun1(X1,X2,X3,X4)=X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_funct_2)).
% 0.13/0.41  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.13/0.41  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.13/0.41  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.41  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.41  fof(c_0_17, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.41  fof(c_0_18, plain, ![X44, X45, X46]:((~r1_tarski(u1_struct_0(X45),u1_struct_0(X46))|m1_pre_topc(X45,X46)|~m1_pre_topc(X46,X44)|~m1_pre_topc(X45,X44)|(~v2_pre_topc(X44)|~l1_pre_topc(X44)))&(~m1_pre_topc(X45,X46)|r1_tarski(u1_struct_0(X45),u1_struct_0(X46))|~m1_pre_topc(X46,X44)|~m1_pre_topc(X45,X44)|(~v2_pre_topc(X44)|~l1_pre_topc(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.13/0.41  cnf(c_0_19, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.41  fof(c_0_20, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t96_tmap_1])).
% 0.13/0.41  cnf(c_0_21, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.41  cnf(c_0_22, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_19])).
% 0.13/0.41  fof(c_0_23, negated_conjecture, ![X59]:(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk4_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))))&((~m1_subset_1(X59,u1_struct_0(esk4_0))|(~r2_hidden(X59,u1_struct_0(esk5_0))|X59=k1_funct_1(esk6_0,X59)))&~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k4_tmap_1(esk4_0,esk5_0),esk6_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])])).
% 0.13/0.41  fof(c_0_24, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_pre_topc(X31,X30)|l1_pre_topc(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.41  fof(c_0_25, plain, ![X27, X28]:(~v2_pre_topc(X27)|~l1_pre_topc(X27)|(~m1_pre_topc(X28,X27)|v2_pre_topc(X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.13/0.41  fof(c_0_26, plain, ![X47, X48, X49, X50, X51]:((m1_subset_1(esk3_5(X47,X48,X49,X50,X51),u1_struct_0(X48))|r2_funct_2(u1_struct_0(X49),u1_struct_0(X47),k2_tmap_1(X48,X47,X50,X49),X51)|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X47))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X47)))))|(~v1_funct_1(X50)|~v1_funct_2(X50,u1_struct_0(X48),u1_struct_0(X47))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X47)))))|(v2_struct_0(X49)|~m1_pre_topc(X49,X48))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)))&((r2_hidden(esk3_5(X47,X48,X49,X50,X51),u1_struct_0(X49))|r2_funct_2(u1_struct_0(X49),u1_struct_0(X47),k2_tmap_1(X48,X47,X50,X49),X51)|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X47))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X47)))))|(~v1_funct_1(X50)|~v1_funct_2(X50,u1_struct_0(X48),u1_struct_0(X47))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X47)))))|(v2_struct_0(X49)|~m1_pre_topc(X49,X48))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)))&(k3_funct_2(u1_struct_0(X48),u1_struct_0(X47),X50,esk3_5(X47,X48,X49,X50,X51))!=k1_funct_1(X51,esk3_5(X47,X48,X49,X50,X51))|r2_funct_2(u1_struct_0(X49),u1_struct_0(X47),k2_tmap_1(X48,X47,X50,X49),X51)|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X47))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X47)))))|(~v1_funct_1(X50)|~v1_funct_2(X50,u1_struct_0(X48),u1_struct_0(X47))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X47)))))|(v2_struct_0(X49)|~m1_pre_topc(X49,X48))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).
% 0.13/0.41  cnf(c_0_27, plain, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.41  cnf(c_0_28, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.41  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.41  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.41  cnf(c_0_31, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.41  cnf(c_0_32, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.41  fof(c_0_33, plain, ![X40, X41]:(((v1_funct_1(k4_tmap_1(X40,X41))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|~m1_pre_topc(X41,X40)))&(v1_funct_2(k4_tmap_1(X40,X41),u1_struct_0(X41),u1_struct_0(X40))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|~m1_pre_topc(X41,X40))))&(m1_subset_1(k4_tmap_1(X40,X41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X40))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|~m1_pre_topc(X41,X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).
% 0.13/0.41  fof(c_0_34, plain, ![X36, X37, X38, X39]:(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|(~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))|(~m1_pre_topc(X39,X36)|k2_tmap_1(X36,X37,X38,X39)=k2_partfun1(u1_struct_0(X36),u1_struct_0(X37),X38,u1_struct_0(X39)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.13/0.41  cnf(c_0_35, plain, (r2_hidden(esk3_5(X1,X2,X3,X4,X5),u1_struct_0(X3))|r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.41  cnf(c_0_36, negated_conjecture, (m1_pre_topc(esk5_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])])).
% 0.13/0.41  cnf(c_0_37, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_28]), c_0_29])])).
% 0.13/0.41  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_28]), c_0_29]), c_0_30])])).
% 0.13/0.41  cnf(c_0_39, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.41  cnf(c_0_40, plain, (v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.41  cnf(c_0_41, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.41  cnf(c_0_42, plain, (m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.41  cnf(c_0_43, plain, (v1_funct_1(k4_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.41  cnf(c_0_44, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.41  cnf(c_0_45, plain, (m1_subset_1(esk3_5(X1,X2,X3,X4,X5),u1_struct_0(X2))|r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.41  cnf(c_0_46, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(X1),k2_tmap_1(esk5_0,X1,X2,esk5_0),X3)|r2_hidden(esk3_5(X1,esk5_0,esk5_0,X2,X3),u1_struct_0(esk5_0))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~v1_funct_2(X3,u1_struct_0(esk5_0),u1_struct_0(X1))|~v1_funct_2(X2,u1_struct_0(esk5_0),u1_struct_0(X1))|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])]), c_0_39])).
% 0.13/0.41  cnf(c_0_47, negated_conjecture, (v1_funct_2(k4_tmap_1(esk4_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_28]), c_0_29]), c_0_30])]), c_0_41])).
% 0.13/0.41  cnf(c_0_48, negated_conjecture, (m1_subset_1(k4_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_28]), c_0_29]), c_0_30])]), c_0_41])).
% 0.13/0.41  cnf(c_0_49, negated_conjecture, (v1_funct_1(k4_tmap_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_28]), c_0_29]), c_0_30])]), c_0_41])).
% 0.13/0.41  cnf(c_0_50, negated_conjecture, (k2_tmap_1(esk5_0,X1,X2,esk5_0)=k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(X1),X2,u1_struct_0(esk5_0))|v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk5_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_36]), c_0_37]), c_0_38])]), c_0_39])).
% 0.13/0.41  cnf(c_0_51, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.41  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.41  cnf(c_0_53, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.41  fof(c_0_54, plain, ![X13, X14, X15, X16]:(v1_xboole_0(X13)|~v1_funct_1(X15)|~v1_funct_2(X15,X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|~m1_subset_1(X16,X13)|k3_funct_2(X13,X14,X15,X16)=k1_funct_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.13/0.41  cnf(c_0_55, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(X1),k2_tmap_1(esk5_0,X1,X2,esk5_0),X3)|m1_subset_1(esk3_5(X1,esk5_0,esk5_0,X2,X3),u1_struct_0(esk5_0))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~v1_funct_2(X3,u1_struct_0(esk5_0),u1_struct_0(X1))|~v1_funct_2(X2,u1_struct_0(esk5_0),u1_struct_0(X1))|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_36]), c_0_37]), c_0_38])]), c_0_39])).
% 0.13/0.41  fof(c_0_56, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.41  cnf(c_0_57, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk5_0,esk4_0,X1,esk5_0),k4_tmap_1(esk4_0,esk5_0))|r2_hidden(esk3_5(esk4_0,esk5_0,esk5_0,X1,k4_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))|~v1_funct_2(X1,u1_struct_0(esk5_0),u1_struct_0(esk4_0))|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_29]), c_0_30]), c_0_48]), c_0_49])]), c_0_41])).
% 0.13/0.41  cnf(c_0_58, negated_conjecture, (k2_tmap_1(esk5_0,esk4_0,esk6_0,esk5_0)=k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_29]), c_0_30]), c_0_52]), c_0_53])]), c_0_41])).
% 0.13/0.41  fof(c_0_59, plain, ![X33, X34, X35]:(v2_struct_0(X33)|~l1_pre_topc(X33)|(v2_struct_0(X34)|~m1_pre_topc(X34,X33)|(~m1_subset_1(X35,u1_struct_0(X34))|m1_subset_1(X35,u1_struct_0(X33))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.13/0.41  cnf(c_0_60, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.41  cnf(c_0_61, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk5_0,esk4_0,X1,esk5_0),k4_tmap_1(esk4_0,esk5_0))|m1_subset_1(esk3_5(esk4_0,esk5_0,esk5_0,X1,k4_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))|~v1_funct_2(X1,u1_struct_0(esk5_0),u1_struct_0(esk4_0))|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_47]), c_0_29]), c_0_30]), c_0_48]), c_0_49])]), c_0_41])).
% 0.13/0.41  cnf(c_0_62, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.41  cnf(c_0_63, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))|r2_hidden(esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_51]), c_0_58]), c_0_52]), c_0_53])])).
% 0.13/0.41  cnf(c_0_64, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.41  fof(c_0_65, plain, ![X53, X54, X55]:(v2_struct_0(X53)|~v2_pre_topc(X53)|~l1_pre_topc(X53)|(v2_struct_0(X54)|~m1_pre_topc(X54,X53)|(~m1_subset_1(X55,u1_struct_0(X53))|(~r2_hidden(X55,u1_struct_0(X54))|k1_funct_1(k4_tmap_1(X53,X54),X55)=X55)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).
% 0.13/0.41  fof(c_0_66, plain, ![X21, X22, X23, X24, X25]:((m1_subset_1(esk2_5(X21,X22,X23,X24,X25),X21)|k2_partfun1(X21,X22,X23,X24)=X25|(~v1_funct_1(X25)|~v1_funct_2(X25,X24,X22)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X24,X22))))|(v1_xboole_0(X24)|~m1_subset_1(X24,k1_zfmisc_1(X21)))|(~v1_funct_1(X23)|~v1_funct_2(X23,X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))|v1_xboole_0(X22)|v1_xboole_0(X21))&((r2_hidden(esk2_5(X21,X22,X23,X24,X25),X24)|k2_partfun1(X21,X22,X23,X24)=X25|(~v1_funct_1(X25)|~v1_funct_2(X25,X24,X22)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X24,X22))))|(v1_xboole_0(X24)|~m1_subset_1(X24,k1_zfmisc_1(X21)))|(~v1_funct_1(X23)|~v1_funct_2(X23,X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))|v1_xboole_0(X22)|v1_xboole_0(X21))&(k3_funct_2(X21,X22,X23,esk2_5(X21,X22,X23,X24,X25))!=k1_funct_1(X25,esk2_5(X21,X22,X23,X24,X25))|k2_partfun1(X21,X22,X23,X24)=X25|(~v1_funct_1(X25)|~v1_funct_2(X25,X24,X22)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X24,X22))))|(v1_xboole_0(X24)|~m1_subset_1(X24,k1_zfmisc_1(X21)))|(~v1_funct_1(X23)|~v1_funct_2(X23,X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))|v1_xboole_0(X22)|v1_xboole_0(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t173_funct_2])])])])])])).
% 0.13/0.41  fof(c_0_67, plain, ![X42, X43]:(~l1_pre_topc(X42)|(~m1_pre_topc(X43,X42)|m1_subset_1(u1_struct_0(X43),k1_zfmisc_1(u1_struct_0(X42))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.13/0.41  cnf(c_0_68, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,X1)=k1_funct_1(esk6_0,X1)|v1_xboole_0(u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_51]), c_0_52]), c_0_53])])).
% 0.13/0.41  cnf(c_0_69, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))|m1_subset_1(esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_51]), c_0_58]), c_0_52]), c_0_53])])).
% 0.13/0.41  cnf(c_0_70, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))|~v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.13/0.41  cnf(c_0_71, negated_conjecture, (X1=k1_funct_1(esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.41  cnf(c_0_72, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_28]), c_0_29])]), c_0_39]), c_0_41])).
% 0.13/0.41  cnf(c_0_73, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_funct_1(k4_tmap_1(X1,X2),X3)=X3|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.41  cnf(c_0_74, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X1)|k2_partfun1(X1,X2,X3,X4)=X5|v1_xboole_0(X4)|v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.13/0.41  cnf(c_0_75, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.41  cnf(c_0_76, plain, (r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X3,X4),X5)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_5(X2,X1,X4,X3,X5))!=k1_funct_1(X5,esk3_5(X2,X1,X4,X3,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.41  cnf(c_0_77, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)))=k1_funct_1(esk6_0,esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)))|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.13/0.41  cnf(c_0_78, negated_conjecture, (k1_funct_1(esk6_0,esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)))=esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0))|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))|~m1_subset_1(esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_71, c_0_63])).
% 0.13/0.41  cnf(c_0_79, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))|m1_subset_1(esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_72, c_0_69])).
% 0.13/0.41  cnf(c_0_80, negated_conjecture, (k1_funct_1(k4_tmap_1(X1,esk5_0),esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)))=esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0))|v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))|~m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)),u1_struct_0(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_63]), c_0_39])).
% 0.13/0.41  cnf(c_0_81, negated_conjecture, (k2_partfun1(X1,u1_struct_0(esk4_0),X2,u1_struct_0(esk5_0))=esk6_0|m1_subset_1(esk2_5(X1,u1_struct_0(esk4_0),X2,u1_struct_0(esk5_0),esk6_0),X1)|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk4_0))))|~m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(X1))|~v1_funct_2(X2,X1,u1_struct_0(esk4_0))|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_51]), c_0_52]), c_0_53])])).
% 0.13/0.41  cnf(c_0_82, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_36]), c_0_37])])).
% 0.13/0.41  fof(c_0_83, plain, ![X17, X18, X19, X20]:((~r2_funct_2(X17,X18,X19,X20)|X19=X20|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|~v1_funct_1(X20)|~v1_funct_2(X20,X17,X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&(X19!=X20|r2_funct_2(X17,X18,X19,X20)|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|~v1_funct_1(X20)|~v1_funct_2(X20,X17,X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.13/0.41  cnf(c_0_84, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))|k1_funct_1(esk6_0,esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)))!=k1_funct_1(k4_tmap_1(esk4_0,esk5_0),esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_58]), c_0_36]), c_0_29]), c_0_37]), c_0_30]), c_0_38]), c_0_48]), c_0_52]), c_0_47]), c_0_51]), c_0_49]), c_0_53])]), c_0_39]), c_0_41])).
% 0.13/0.41  cnf(c_0_85, negated_conjecture, (k1_funct_1(esk6_0,esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)))=esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0))|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.13/0.41  cnf(c_0_86, negated_conjecture, (k1_funct_1(k4_tmap_1(esk4_0,esk5_0),esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0)))=esk3_5(esk4_0,esk5_0,esk5_0,esk6_0,k4_tmap_1(esk4_0,esk5_0))|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_28]), c_0_29]), c_0_30])]), c_0_41]), c_0_79])).
% 0.13/0.41  cnf(c_0_87, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0))=esk6_0|m1_subset_1(esk2_5(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_51]), c_0_52]), c_0_82]), c_0_53])])).
% 0.13/0.41  cnf(c_0_88, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.13/0.41  cnf(c_0_89, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.13/0.41  cnf(c_0_90, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k4_tmap_1(esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])).
% 0.13/0.41  cnf(c_0_91, plain, (k2_partfun1(X1,X2,X3,X4)=X5|v1_xboole_0(X4)|v1_xboole_0(X2)|v1_xboole_0(X1)|k3_funct_2(X1,X2,X3,esk2_5(X1,X2,X3,X4,X5))!=k1_funct_1(X5,esk2_5(X1,X2,X3,X4,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.13/0.41  cnf(c_0_92, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,esk2_5(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0),esk6_0))=k1_funct_1(esk6_0,esk2_5(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0),esk6_0))|k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0))=esk6_0|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_68, c_0_87])).
% 0.13/0.41  cnf(c_0_93, plain, (r2_funct_2(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)), inference(er,[status(thm)],[c_0_88])).
% 0.13/0.41  cnf(c_0_94, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0))=k4_tmap_1(esk4_0,esk5_0)|~m1_subset_1(k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))|~v1_funct_2(k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk4_0))|~v1_funct_1(k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_48]), c_0_47]), c_0_49])])).
% 0.13/0.41  cnf(c_0_95, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,u1_struct_0(esk5_0))=esk6_0|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_52]), c_0_82]), c_0_51]), c_0_53])])).
% 0.13/0.41  cnf(c_0_96, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k4_tmap_1(esk4_0,esk5_0),k4_tmap_1(esk4_0,esk5_0))|~m1_subset_1(k4_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_47]), c_0_49])])).
% 0.13/0.41  fof(c_0_97, plain, ![X32]:(v2_struct_0(X32)|~l1_struct_0(X32)|~v1_xboole_0(u1_struct_0(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.41  cnf(c_0_98, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k4_tmap_1(esk4_0,esk5_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.41  cnf(c_0_99, negated_conjecture, (esk6_0=k4_tmap_1(esk4_0,esk5_0)|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_52]), c_0_51]), c_0_53])])).
% 0.13/0.41  cnf(c_0_100, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k4_tmap_1(esk4_0,esk5_0),k4_tmap_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_48])])).
% 0.13/0.41  cnf(c_0_101, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.13/0.41  cnf(c_0_102, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100])])).
% 0.13/0.41  fof(c_0_103, plain, ![X29]:(~l1_pre_topc(X29)|l1_struct_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.41  cnf(c_0_104, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_39])).
% 0.13/0.41  cnf(c_0_105, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.13/0.41  cnf(c_0_106, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_37])])).
% 0.13/0.41  cnf(c_0_107, negated_conjecture, (~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_106]), c_0_41])).
% 0.13/0.41  cnf(c_0_108, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_105]), c_0_29])]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 109
% 0.13/0.41  # Proof object clause steps            : 74
% 0.13/0.41  # Proof object formula steps           : 35
% 0.13/0.41  # Proof object conjectures             : 52
% 0.13/0.41  # Proof object clause conjectures      : 49
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 32
% 0.13/0.41  # Proof object initial formulas used   : 17
% 0.13/0.41  # Proof object generating inferences   : 39
% 0.13/0.41  # Proof object simplifying inferences  : 124
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 17
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 37
% 0.13/0.41  # Removed in clause preprocessing      : 0
% 0.13/0.41  # Initial clauses in saturation        : 37
% 0.13/0.41  # Processed clauses                    : 228
% 0.13/0.41  # ...of these trivial                  : 0
% 0.13/0.41  # ...subsumed                          : 1
% 0.13/0.41  # ...remaining for further processing  : 227
% 0.13/0.41  # Other redundant clauses eliminated   : 3
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 50
% 0.13/0.41  # Backward-rewritten                   : 35
% 0.13/0.41  # Generated clauses                    : 223
% 0.13/0.41  # ...of the previous two non-trivial   : 206
% 0.13/0.41  # Contextual simplify-reflections      : 18
% 0.13/0.41  # Paramodulations                      : 220
% 0.13/0.41  # Factorizations                       : 0
% 0.13/0.41  # Equation resolutions                 : 3
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 103
% 0.13/0.41  #    Positive orientable unit clauses  : 28
% 0.13/0.41  #    Positive unorientable unit clauses: 0
% 0.13/0.41  #    Negative unit clauses             : 4
% 0.13/0.41  #    Non-unit-clauses                  : 71
% 0.13/0.41  # Current number of unprocessed clauses: 45
% 0.13/0.41  # ...number of literals in the above   : 178
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 121
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 6618
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 509
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 69
% 0.13/0.41  # Unit Clause-clause subsumption calls : 179
% 0.13/0.41  # Rewrite failures with RHS unbound    : 0
% 0.13/0.41  # BW rewrite match attempts            : 41
% 0.13/0.41  # BW rewrite match successes           : 6
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 17812
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.061 s
% 0.13/0.41  # System time              : 0.004 s
% 0.13/0.41  # Total time               : 0.065 s
% 0.13/0.41  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
