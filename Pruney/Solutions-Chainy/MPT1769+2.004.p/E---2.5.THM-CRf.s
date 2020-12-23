%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:42 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  114 (1224 expanded)
%              Number of clauses        :   83 ( 418 expanded)
%              Number of leaves         :   15 ( 285 expanded)
%              Depth                    :   16
%              Number of atoms          :  599 (18472 expanded)
%              Number of equality atoms :   30 ( 823 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t80_tmap_1,conjecture,(
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
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                         => ! [X7] :
                              ( ( v1_funct_1(X7)
                                & v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))
                                & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                             => ( ( X4 = X1
                                  & r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7) )
                               => ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)
                                <=> r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).

fof(t78_tmap_1,axiom,(
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
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X3,X4)
                       => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(dt_k3_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_pre_topc(X3,X1)
        & m1_pre_topc(X4,X1)
        & v1_funct_1(X5)
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
     => ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
        & v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(redefinition_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( r1_funct_2(X1,X2,X3,X4,X5,X6)
      <=> X5 = X6 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

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
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                           => ! [X7] :
                                ( ( v1_funct_1(X7)
                                  & v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                               => ( ( X4 = X1
                                    & r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7) )
                                 => ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)
                                  <=> r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t80_tmap_1])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    & esk4_0 = esk1_0
    & r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0)
    & ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)
      | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) )
    & ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)
      | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_17,plain,(
    ! [X47,X48,X49,X50,X51] :
      ( v2_struct_0(X47)
      | ~ v2_pre_topc(X47)
      | ~ l1_pre_topc(X47)
      | v2_struct_0(X48)
      | ~ v2_pre_topc(X48)
      | ~ l1_pre_topc(X48)
      | v2_struct_0(X49)
      | ~ m1_pre_topc(X49,X47)
      | v2_struct_0(X50)
      | ~ m1_pre_topc(X50,X47)
      | ~ v1_funct_1(X51)
      | ~ v1_funct_2(X51,u1_struct_0(X47),u1_struct_0(X48))
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
      | ~ m1_pre_topc(X49,X50)
      | r2_funct_2(u1_struct_0(X49),u1_struct_0(X48),k3_tmap_1(X47,X48,X50,X49,k2_tmap_1(X47,X48,X51,X50)),k2_tmap_1(X47,X48,X51,X49)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_tmap_1])])])])).

fof(c_0_18,plain,(
    ! [X52,X53,X54] :
      ( ~ v2_pre_topc(X52)
      | ~ l1_pre_topc(X52)
      | ~ m1_pre_topc(X53,X52)
      | ~ m1_pre_topc(X54,X53)
      | m1_pre_topc(X54,X52) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_19,plain,(
    ! [X13,X14,X15] :
      ( ( v4_relat_1(X15,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v5_relat_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( esk4_0 = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | v1_relat_1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,plain,(
    ! [X34,X35,X36,X37] :
      ( v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | ~ v1_funct_1(X36)
      | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35))))
      | ~ m1_pre_topc(X37,X34)
      | k2_tmap_1(X34,X35,X36,X37) = k2_partfun1(u1_struct_0(X34),u1_struct_0(X35),X36,u1_struct_0(X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

fof(c_0_27,plain,(
    ! [X16,X17,X18,X19] :
      ( ~ v1_funct_1(X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k2_partfun1(X16,X17,X18,X19) = k7_relat_1(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_28,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X9)
      | ~ v4_relat_1(X9,X8)
      | X9 = k7_relat_1(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_29,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X42,X43,X44,X45,X46] :
      ( ( v1_funct_1(k3_tmap_1(X42,X43,X44,X45,X46))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43)
        | ~ m1_pre_topc(X44,X42)
        | ~ m1_pre_topc(X45,X42)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43)))) )
      & ( v1_funct_2(k3_tmap_1(X42,X43,X44,X45,X46),u1_struct_0(X45),u1_struct_0(X43))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43)
        | ~ m1_pre_topc(X44,X42)
        | ~ m1_pre_topc(X45,X42)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43)))) )
      & ( m1_subset_1(k3_tmap_1(X42,X43,X44,X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X43))))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43)
        | ~ m1_pre_topc(X44,X42)
        | ~ m1_pre_topc(X45,X42)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( v4_relat_1(esk7_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_45,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_49,plain,(
    ! [X38,X39,X40,X41] :
      ( ( v1_funct_1(k2_tmap_1(X38,X39,X40,X41))
        | ~ l1_struct_0(X38)
        | ~ l1_struct_0(X39)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))
        | ~ l1_struct_0(X41) )
      & ( v1_funct_2(k2_tmap_1(X38,X39,X40,X41),u1_struct_0(X41),u1_struct_0(X39))
        | ~ l1_struct_0(X38)
        | ~ l1_struct_0(X39)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))
        | ~ l1_struct_0(X41) )
      & ( m1_subset_1(k2_tmap_1(X38,X39,X40,X41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X39))))
        | ~ l1_struct_0(X38)
        | ~ l1_struct_0(X39)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))
        | ~ l1_struct_0(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_50,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(esk1_0,X1,esk1_0,X2,k2_tmap_1(esk1_0,X1,X3,esk1_0)),k2_tmap_1(esk1_0,X1,X3,X2))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X3,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_52,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(X1),X2,u1_struct_0(esk1_0)) = k2_tmap_1(esk1_0,X1,X2,esk1_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_21])).

cnf(c_0_54,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,X1) = k7_relat_1(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_30]),c_0_41])])).

cnf(c_0_55,negated_conjecture,
    ( k7_relat_1(esk7_0,u1_struct_0(esk1_0)) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_56,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_57,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_59,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(esk1_0,X1,X2,esk3_0,X3),u1_struct_0(esk3_0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_60,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(esk1_0,X1,X2,esk3_0,X3))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_46]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_61,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(esk1_0,X1,X2,esk3_0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_46]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_62,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_63,plain,(
    ! [X24] :
      ( ~ l1_pre_topc(X24)
      | l1_struct_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_64,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_65,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_66,plain,(
    ! [X20,X21,X22,X23] :
      ( ( ~ r2_funct_2(X20,X21,X22,X23)
        | X22 = X23
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( X22 != X23
        | r2_funct_2(X20,X21,X22,X23)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_67,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(X1),k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,k2_tmap_1(esk1_0,X1,X2,esk1_0)),k2_tmap_1(esk1_0,X1,X2,esk3_0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_46]),c_0_51])).

cnf(c_0_68,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk7_0,esk1_0) = esk7_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_41]),c_0_30])]),c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2),u1_struct_0(esk3_0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_34])).

cnf(c_0_70,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_34])).

cnf(c_0_71,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_34])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_53]),c_0_41]),c_0_30])])).

cnf(c_0_73,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_53]),c_0_41]),c_0_30])])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_53]),c_0_41]),c_0_30])])).

cnf(c_0_76,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_77,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_53]),c_0_68]),c_0_56]),c_0_57]),c_0_41]),c_0_30])]),c_0_58])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_53]),c_0_56]),c_0_57]),c_0_41]),c_0_30])]),c_0_58])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_53]),c_0_56]),c_0_57]),c_0_41]),c_0_30])]),c_0_58])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_53]),c_0_56]),c_0_57]),c_0_41]),c_0_30])]),c_0_58])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_57])])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_73]),c_0_57])])).

cnf(c_0_83,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_73]),c_0_57])])).

fof(c_0_84,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_pre_topc(X26,X25)
      | l1_pre_topc(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_85,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0) = k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_79]),c_0_80])])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_73]),c_0_36])])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_73]),c_0_36])])).

cnf(c_0_88,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_73]),c_0_36])])).

cnf(c_0_89,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

fof(c_0_90,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( ~ r1_funct_2(X28,X29,X30,X31,X32,X33)
        | X32 = X33
        | v1_xboole_0(X29)
        | v1_xboole_0(X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X28,X29)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X32 != X33
        | r1_funct_2(X28,X29,X30,X31,X32,X33)
        | v1_xboole_0(X29)
        | v1_xboole_0(X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X28,X29)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_91,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_93,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0) = k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87]),c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_46]),c_0_36])])).

cnf(c_0_95,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_96,plain,
    ( X5 = X6
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ r1_funct_2(X1,X2,X3,X4,X5,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_91,c_0_21])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_101,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),esk6_0)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_92,c_0_21])).

cnf(c_0_102,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0) = k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_73]),c_0_94])])).

cnf(c_0_103,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),esk6_0)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_95,c_0_21])).

cnf(c_0_104,negated_conjecture,
    ( esk7_0 = esk5_0
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_53]),c_0_98]),c_0_41]),c_0_99]),c_0_30]),c_0_100])])).

cnf(c_0_105,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),esk6_0)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_101,c_0_102])).

fof(c_0_106,plain,(
    ! [X27] :
      ( v2_struct_0(X27)
      | ~ l1_struct_0(X27)
      | ~ v1_xboole_0(u1_struct_0(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_107,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),esk6_0)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_108,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_104])).

cnf(c_0_110,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])).

cnf(c_0_112,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_58])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_73]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:44:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.48  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.20/0.48  # and selection function SelectCQIPrecWNTNp.
% 0.20/0.48  #
% 0.20/0.48  # Preprocessing time       : 0.023 s
% 0.20/0.48  # Presaturation interreduction done
% 0.20/0.48  
% 0.20/0.48  # Proof found!
% 0.20/0.48  # SZS status Theorem
% 0.20/0.48  # SZS output start CNFRefutation
% 0.20/0.48  fof(t80_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tmap_1)).
% 0.20/0.48  fof(t78_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tmap_1)).
% 0.20/0.48  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.20/0.48  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.48  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.48  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.20/0.48  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.20/0.48  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.20/0.48  fof(dt_k3_tmap_1, axiom, ![X1, X2, X3, X4, X5]:(((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&m1_pre_topc(X3,X1))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))&v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 0.20/0.48  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 0.20/0.48  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.48  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.20/0.48  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.48  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.20/0.48  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.48  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6))))))))))), inference(assume_negation,[status(cth)],[t80_tmap_1])).
% 0.20/0.48  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&((esk4_0=esk1_0&r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0))&((~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0))&(r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.20/0.48  fof(c_0_17, plain, ![X47, X48, X49, X50, X51]:(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)|(v2_struct_0(X49)|~m1_pre_topc(X49,X47)|(v2_struct_0(X50)|~m1_pre_topc(X50,X47)|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X47),u1_struct_0(X48))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))|(~m1_pre_topc(X49,X50)|r2_funct_2(u1_struct_0(X49),u1_struct_0(X48),k3_tmap_1(X47,X48,X50,X49,k2_tmap_1(X47,X48,X51,X50)),k2_tmap_1(X47,X48,X51,X49)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_tmap_1])])])])).
% 0.20/0.48  fof(c_0_18, plain, ![X52, X53, X54]:(~v2_pre_topc(X52)|~l1_pre_topc(X52)|(~m1_pre_topc(X53,X52)|(~m1_pre_topc(X54,X53)|m1_pre_topc(X54,X52)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.20/0.48  fof(c_0_19, plain, ![X13, X14, X15]:((v4_relat_1(X15,X13)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))&(v5_relat_1(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.48  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_21, negated_conjecture, (esk4_0=esk1_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  fof(c_0_22, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|v1_relat_1(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.48  cnf(c_0_23, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.48  cnf(c_0_24, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.48  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  fof(c_0_26, plain, ![X34, X35, X36, X37]:(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35))))|(~m1_pre_topc(X37,X34)|k2_tmap_1(X34,X35,X36,X37)=k2_partfun1(u1_struct_0(X34),u1_struct_0(X35),X36,u1_struct_0(X37)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.20/0.48  fof(c_0_27, plain, ![X16, X17, X18, X19]:(~v1_funct_1(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|k2_partfun1(X16,X17,X18,X19)=k7_relat_1(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.20/0.48  fof(c_0_28, plain, ![X8, X9]:(~v1_relat_1(X9)|~v4_relat_1(X9,X8)|X9=k7_relat_1(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.20/0.48  cnf(c_0_29, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.48  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.48  cnf(c_0_31, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.48  fof(c_0_32, plain, ![X42, X43, X44, X45, X46]:(((v1_funct_1(k3_tmap_1(X42,X43,X44,X45,X46))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|~m1_pre_topc(X44,X42)|~m1_pre_topc(X45,X42)|~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43))))))&(v1_funct_2(k3_tmap_1(X42,X43,X44,X45,X46),u1_struct_0(X45),u1_struct_0(X43))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|~m1_pre_topc(X44,X42)|~m1_pre_topc(X45,X42)|~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43)))))))&(m1_subset_1(k3_tmap_1(X42,X43,X44,X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X43))))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|~m1_pre_topc(X44,X42)|~m1_pre_topc(X45,X42)|~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).
% 0.20/0.48  cnf(c_0_33, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X3,X4)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.48  cnf(c_0_34, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(rw,[status(thm)],[c_0_25, c_0_21])).
% 0.20/0.48  cnf(c_0_35, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_36, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_37, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_38, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.48  cnf(c_0_39, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_40, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.48  cnf(c_0_41, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_42, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.48  cnf(c_0_43, negated_conjecture, (v4_relat_1(esk7_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.48  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 0.20/0.48  cnf(c_0_45, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.48  cnf(c_0_46, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_47, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.48  cnf(c_0_48, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.48  fof(c_0_49, plain, ![X38, X39, X40, X41]:(((v1_funct_1(k2_tmap_1(X38,X39,X40,X41))|(~l1_struct_0(X38)|~l1_struct_0(X39)|~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))|~l1_struct_0(X41)))&(v1_funct_2(k2_tmap_1(X38,X39,X40,X41),u1_struct_0(X41),u1_struct_0(X39))|(~l1_struct_0(X38)|~l1_struct_0(X39)|~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))|~l1_struct_0(X41))))&(m1_subset_1(k2_tmap_1(X38,X39,X40,X41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X39))))|(~l1_struct_0(X38)|~l1_struct_0(X39)|~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))|~l1_struct_0(X41)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 0.20/0.48  cnf(c_0_50, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(esk1_0,X1,esk1_0,X2,k2_tmap_1(esk1_0,X1,X3,esk1_0)),k2_tmap_1(esk1_0,X1,X3,X2))|~v2_pre_topc(X1)|~m1_pre_topc(X2,esk1_0)|~l1_pre_topc(X1)|~v1_funct_2(X3,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.20/0.48  cnf(c_0_51, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_52, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(X1),X2,u1_struct_0(esk1_0))=k2_tmap_1(esk1_0,X1,X2,esk1_0)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.20/0.48  cnf(c_0_53, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_39, c_0_21])).
% 0.20/0.48  cnf(c_0_54, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,X1)=k7_relat_1(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_30]), c_0_41])])).
% 0.20/0.48  cnf(c_0_55, negated_conjecture, (k7_relat_1(esk7_0,u1_struct_0(esk1_0))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.20/0.48  cnf(c_0_56, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_57, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_58, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_59, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(esk1_0,X1,X2,esk3_0,X3),u1_struct_0(esk3_0),u1_struct_0(X1))|~v2_pre_topc(X1)|~m1_pre_topc(X2,esk1_0)|~l1_pre_topc(X1)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_35]), c_0_36])]), c_0_37])).
% 0.20/0.48  cnf(c_0_60, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(esk1_0,X1,X2,esk3_0,X3))|~v2_pre_topc(X1)|~m1_pre_topc(X2,esk1_0)|~l1_pre_topc(X1)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_46]), c_0_35]), c_0_36])]), c_0_37])).
% 0.20/0.48  cnf(c_0_61, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(esk1_0,X1,X2,esk3_0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1))))|~v2_pre_topc(X1)|~m1_pre_topc(X2,esk1_0)|~l1_pre_topc(X1)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_46]), c_0_35]), c_0_36])]), c_0_37])).
% 0.20/0.48  cnf(c_0_62, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.48  fof(c_0_63, plain, ![X24]:(~l1_pre_topc(X24)|l1_struct_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.48  cnf(c_0_64, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.48  cnf(c_0_65, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.48  fof(c_0_66, plain, ![X20, X21, X22, X23]:((~r2_funct_2(X20,X21,X22,X23)|X22=X23|(~v1_funct_1(X22)|~v1_funct_2(X22,X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~v1_funct_1(X23)|~v1_funct_2(X23,X20,X21)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))&(X22!=X23|r2_funct_2(X20,X21,X22,X23)|(~v1_funct_1(X22)|~v1_funct_2(X22,X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~v1_funct_1(X23)|~v1_funct_2(X23,X20,X21)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.20/0.48  cnf(c_0_67, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(X1),k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,k2_tmap_1(esk1_0,X1,X2,esk1_0)),k2_tmap_1(esk1_0,X1,X2,esk3_0))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_46]), c_0_51])).
% 0.20/0.48  cnf(c_0_68, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk7_0,esk1_0)=esk7_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_41]), c_0_30])]), c_0_58])).
% 0.20/0.48  cnf(c_0_69, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2),u1_struct_0(esk3_0),u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_59, c_0_34])).
% 0.20/0.48  cnf(c_0_70, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_60, c_0_34])).
% 0.20/0.48  cnf(c_0_71, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_61, c_0_34])).
% 0.20/0.48  cnf(c_0_72, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_53]), c_0_41]), c_0_30])])).
% 0.20/0.48  cnf(c_0_73, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.48  cnf(c_0_74, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_53]), c_0_41]), c_0_30])])).
% 0.20/0.48  cnf(c_0_75, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_53]), c_0_41]), c_0_30])])).
% 0.20/0.48  cnf(c_0_76, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.48  cnf(c_0_77, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_53]), c_0_68]), c_0_56]), c_0_57]), c_0_41]), c_0_30])]), c_0_58])).
% 0.20/0.48  cnf(c_0_78, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_53]), c_0_56]), c_0_57]), c_0_41]), c_0_30])]), c_0_58])).
% 0.20/0.48  cnf(c_0_79, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_53]), c_0_56]), c_0_57]), c_0_41]), c_0_30])]), c_0_58])).
% 0.20/0.48  cnf(c_0_80, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_53]), c_0_56]), c_0_57]), c_0_41]), c_0_30])]), c_0_58])).
% 0.20/0.48  cnf(c_0_81, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_57])])).
% 0.20/0.48  cnf(c_0_82, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_73]), c_0_57])])).
% 0.20/0.48  cnf(c_0_83, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1))|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_73]), c_0_57])])).
% 0.20/0.48  fof(c_0_84, plain, ![X25, X26]:(~l1_pre_topc(X25)|(~m1_pre_topc(X26,X25)|l1_pre_topc(X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.48  cnf(c_0_85, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0)=k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_79]), c_0_80])])).
% 0.20/0.48  cnf(c_0_86, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_73]), c_0_36])])).
% 0.20/0.48  cnf(c_0_87, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_73]), c_0_36])])).
% 0.20/0.48  cnf(c_0_88, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_73]), c_0_36])])).
% 0.20/0.48  cnf(c_0_89, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.20/0.48  fof(c_0_90, plain, ![X28, X29, X30, X31, X32, X33]:((~r1_funct_2(X28,X29,X30,X31,X32,X33)|X32=X33|(v1_xboole_0(X29)|v1_xboole_0(X31)|~v1_funct_1(X32)|~v1_funct_2(X32,X28,X29)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(X32!=X33|r1_funct_2(X28,X29,X30,X31,X32,X33)|(v1_xboole_0(X29)|v1_xboole_0(X31)|~v1_funct_1(X32)|~v1_funct_2(X32,X28,X29)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.20/0.48  cnf(c_0_91, negated_conjecture, (r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_92, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_93, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0)=k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)|~l1_struct_0(esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87]), c_0_88])).
% 0.20/0.48  cnf(c_0_94, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_46]), c_0_36])])).
% 0.20/0.48  cnf(c_0_95, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_96, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.20/0.48  cnf(c_0_97, negated_conjecture, (r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_91, c_0_21])).
% 0.20/0.48  cnf(c_0_98, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_99, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_100, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_101, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),esk6_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(rw,[status(thm)],[c_0_92, c_0_21])).
% 0.20/0.48  cnf(c_0_102, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0)=k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_73]), c_0_94])])).
% 0.20/0.48  cnf(c_0_103, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),esk6_0)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(rw,[status(thm)],[c_0_95, c_0_21])).
% 0.20/0.48  cnf(c_0_104, negated_conjecture, (esk7_0=esk5_0|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_53]), c_0_98]), c_0_41]), c_0_99]), c_0_30]), c_0_100])])).
% 0.20/0.48  cnf(c_0_105, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),esk6_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(rw,[status(thm)],[c_0_101, c_0_102])).
% 0.20/0.48  fof(c_0_106, plain, ![X27]:(v2_struct_0(X27)|~l1_struct_0(X27)|~v1_xboole_0(u1_struct_0(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.48  cnf(c_0_107, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),esk6_0)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.20/0.48  cnf(c_0_108, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_102, c_0_104])).
% 0.20/0.48  cnf(c_0_109, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(spm,[status(thm)],[c_0_105, c_0_104])).
% 0.20/0.48  cnf(c_0_110, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.20/0.48  cnf(c_0_111, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109])).
% 0.20/0.48  cnf(c_0_112, negated_conjecture, (~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_58])).
% 0.20/0.48  cnf(c_0_113, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_73]), c_0_57])]), ['proof']).
% 0.20/0.48  # SZS output end CNFRefutation
% 0.20/0.48  # Proof object total steps             : 114
% 0.20/0.48  # Proof object clause steps            : 83
% 0.20/0.48  # Proof object formula steps           : 31
% 0.20/0.48  # Proof object conjectures             : 67
% 0.20/0.48  # Proof object clause conjectures      : 64
% 0.20/0.48  # Proof object formula conjectures     : 3
% 0.20/0.48  # Proof object initial clauses used    : 37
% 0.20/0.48  # Proof object initial formulas used   : 15
% 0.20/0.48  # Proof object generating inferences   : 38
% 0.20/0.48  # Proof object simplifying inferences  : 108
% 0.20/0.48  # Training examples: 0 positive, 0 negative
% 0.20/0.48  # Parsed axioms                        : 15
% 0.20/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.48  # Initial clauses                      : 44
% 0.20/0.48  # Removed in clause preprocessing      : 0
% 0.20/0.48  # Initial clauses in saturation        : 44
% 0.20/0.48  # Processed clauses                    : 1124
% 0.20/0.48  # ...of these trivial                  : 61
% 0.20/0.48  # ...subsumed                          : 47
% 0.20/0.48  # ...remaining for further processing  : 1016
% 0.20/0.48  # Other redundant clauses eliminated   : 2
% 0.20/0.48  # Clauses deleted for lack of memory   : 0
% 0.20/0.48  # Backward-subsumed                    : 152
% 0.20/0.48  # Backward-rewritten                   : 223
% 0.20/0.48  # Generated clauses                    : 2298
% 0.20/0.48  # ...of the previous two non-trivial   : 2113
% 0.20/0.48  # Contextual simplify-reflections      : 57
% 0.20/0.48  # Paramodulations                      : 2296
% 0.20/0.48  # Factorizations                       : 0
% 0.20/0.48  # Equation resolutions                 : 2
% 0.20/0.48  # Propositional unsat checks           : 0
% 0.20/0.48  #    Propositional check models        : 0
% 0.20/0.48  #    Propositional check unsatisfiable : 0
% 0.20/0.48  #    Propositional clauses             : 0
% 0.20/0.48  #    Propositional clauses after purity: 0
% 0.20/0.48  #    Propositional unsat core size     : 0
% 0.20/0.48  #    Propositional preprocessing time  : 0.000
% 0.20/0.48  #    Propositional encoding time       : 0.000
% 0.20/0.48  #    Propositional solver time         : 0.000
% 0.20/0.48  #    Success case prop preproc time    : 0.000
% 0.20/0.48  #    Success case prop encoding time   : 0.000
% 0.20/0.48  #    Success case prop solver time     : 0.000
% 0.20/0.48  # Current number of processed clauses  : 596
% 0.20/0.48  #    Positive orientable unit clauses  : 453
% 0.20/0.48  #    Positive unorientable unit clauses: 0
% 0.20/0.48  #    Negative unit clauses             : 4
% 0.20/0.48  #    Non-unit-clauses                  : 139
% 0.20/0.48  # Current number of unprocessed clauses: 1052
% 0.20/0.48  # ...number of literals in the above   : 3220
% 0.20/0.48  # Current number of archived formulas  : 0
% 0.20/0.48  # Current number of archived clauses   : 418
% 0.20/0.48  # Clause-clause subsumption calls (NU) : 19074
% 0.20/0.48  # Rec. Clause-clause subsumption calls : 12150
% 0.20/0.48  # Non-unit clause-clause subsumptions  : 231
% 0.20/0.48  # Unit Clause-clause subsumption calls : 5232
% 0.20/0.48  # Rewrite failures with RHS unbound    : 0
% 0.20/0.48  # BW rewrite match attempts            : 12668
% 0.20/0.48  # BW rewrite match successes           : 58
% 0.20/0.48  # Condensation attempts                : 0
% 0.20/0.48  # Condensation successes               : 0
% 0.20/0.48  # Termbank termtop insertions          : 119966
% 0.20/0.48  
% 0.20/0.48  # -------------------------------------------------
% 0.20/0.48  # User time                : 0.134 s
% 0.20/0.48  # System time              : 0.010 s
% 0.20/0.48  # Total time               : 0.144 s
% 0.20/0.48  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
