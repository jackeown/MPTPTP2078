%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:42 EST 2020

% Result     : Theorem 1.15s
% Output     : CNFRefutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  106 (2311 expanded)
%              Number of clauses        :   83 ( 795 expanded)
%              Number of leaves         :   11 ( 539 expanded)
%              Depth                    :   15
%              Number of atoms          :  550 (34950 expanded)
%              Number of equality atoms :   40 (1574 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

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

fof(c_0_11,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_tarski(X15,X16) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(X18,X19)
        | X18 != X19 )
      & ( r1_tarski(X19,X18)
        | X18 != X19 )
      & ( ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X19,X18)
        | X18 = X19 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_15,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk3_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk3_0)
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))
    & v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,u1_struct_0(esk6_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0))))
    & esk6_0 = esk3_0
    & r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0),u1_struct_0(esk4_0),esk7_0,esk9_0)
    & ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)
      | ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) )
    & ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)
      | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_18,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ r2_funct_2(X30,X31,X32,X33)
        | X32 = X33
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X32 != X33
        | r2_funct_2(X30,X31,X32,X33)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

fof(c_0_21,plain,(
    ! [X49,X50,X51,X52,X53] :
      ( ( v1_funct_1(k3_tmap_1(X49,X50,X51,X52,X53))
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50)
        | ~ m1_pre_topc(X51,X49)
        | ~ m1_pre_topc(X52,X49)
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,u1_struct_0(X51),u1_struct_0(X50))
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X50)))) )
      & ( v1_funct_2(k3_tmap_1(X49,X50,X51,X52,X53),u1_struct_0(X52),u1_struct_0(X50))
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50)
        | ~ m1_pre_topc(X51,X49)
        | ~ m1_pre_topc(X52,X49)
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,u1_struct_0(X51),u1_struct_0(X50))
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X50)))) )
      & ( m1_subset_1(k3_tmap_1(X49,X50,X51,X52,X53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X50))))
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50)
        | ~ m1_pre_topc(X51,X49)
        | ~ m1_pre_topc(X52,X49)
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,u1_struct_0(X51),u1_struct_0(X50))
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X50)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)
    | ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( esk6_0 = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)
    | ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_19])).

cnf(c_0_35,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(esk3_0,X1,X2,esk5_0,X3),u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk9_0,u1_struct_0(esk6_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(esk3_0,X1,X2,esk5_0,X3))
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_44,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_45,plain,(
    ! [X44,X45,X46,X47,X48] :
      ( v2_struct_0(X44)
      | ~ v2_pre_topc(X44)
      | ~ l1_pre_topc(X44)
      | v2_struct_0(X45)
      | ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | ~ m1_pre_topc(X46,X44)
      | ~ m1_pre_topc(X47,X44)
      | ~ v1_funct_1(X48)
      | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45))))
      | ~ m1_pre_topc(X47,X46)
      | k3_tmap_1(X44,X45,X46,X47,X48) = k2_partfun1(u1_struct_0(X46),u1_struct_0(X45),X48,u1_struct_0(X47)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_46,plain,(
    ! [X54,X55,X56] :
      ( ~ v2_pre_topc(X54)
      | ~ l1_pre_topc(X54)
      | ~ m1_pre_topc(X55,X54)
      | ~ m1_pre_topc(X56,X55)
      | m1_pre_topc(X56,X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)
    | ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),X1,esk8_0)
    | ~ v1_xboole_0(k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])])).

fof(c_0_49,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_xboole_0(X27)
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X27)))
      | v1_xboole_0(X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_50,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(esk3_0,X1,esk3_0,esk5_0,X2),u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk3_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(esk9_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_23])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(esk3_0,X1,esk3_0,esk5_0,X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk3_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_58,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(esk3_0,X1,X2,esk5_0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_59,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_61,plain,(
    ! [X40,X41,X42,X43] :
      ( v2_struct_0(X40)
      | ~ v2_pre_topc(X40)
      | ~ l1_pre_topc(X40)
      | v2_struct_0(X41)
      | ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | ~ v1_funct_1(X42)
      | ~ v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X41))
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X41))))
      | ~ m1_pre_topc(X43,X40)
      | k2_tmap_1(X40,X41,X42,X43) = k2_partfun1(u1_struct_0(X40),u1_struct_0(X41),X42,u1_struct_0(X43)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_62,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)
    | ~ v1_xboole_0(k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0))
    | ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),c_0_54]),c_0_55])]),c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_51]),c_0_52]),c_0_53]),c_0_54]),c_0_55])]),c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(esk3_0,X1,esk3_0,esk5_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk3_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_40])).

cnf(c_0_68,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_71,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_23])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),X1)
    | ~ v1_xboole_0(k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0))
    | ~ v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_34])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_38])).

cnf(c_0_74,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0))
    | ~ m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_65]),c_0_66])])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_51]),c_0_52]),c_0_53]),c_0_54]),c_0_55])]),c_0_56])).

cnf(c_0_76,negated_conjecture,
    ( k3_tmap_1(X1,X2,esk3_0,esk5_0,X3) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(X2),X3,u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X3,u1_struct_0(esk3_0),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X2)))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_27])).

cnf(c_0_77,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(X1),X2,u1_struct_0(esk5_0)) = k2_tmap_1(esk3_0,X1,X2,esk5_0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk3_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_81,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0) = esk8_0
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0))
    | ~ m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_36]),c_0_37]),c_0_38])])).

fof(c_0_82,plain,(
    ! [X34,X35,X36,X37,X38,X39] :
      ( ( ~ r1_funct_2(X34,X35,X36,X37,X38,X39)
        | X38 = X39
        | v1_xboole_0(X35)
        | v1_xboole_0(X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X34,X35)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X36,X37)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( X38 != X39
        | r1_funct_2(X34,X35,X36,X37,X38,X39)
        | v1_xboole_0(X35)
        | v1_xboole_0(X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X34,X35)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X36,X37)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_83,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0),u1_struct_0(esk4_0),esk7_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),X1,k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),X2)
    | ~ v1_xboole_0(k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0))
    | ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_34]),c_0_73])).

cnf(c_0_85,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])])).

cnf(c_0_86,negated_conjecture,
    ( v1_xboole_0(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_75])).

cnf(c_0_87,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(X1),X2,u1_struct_0(esk5_0)) = k3_tmap_1(esk3_0,X1,esk3_0,esk5_0,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk3_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_88,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk7_0,u1_struct_0(esk5_0)) = k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_52]),c_0_53]),c_0_79]),c_0_80])]),c_0_56])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_78]),c_0_52]),c_0_53]),c_0_79]),c_0_80])]),c_0_56])).

cnf(c_0_90,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0) = esk8_0
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_66])])).

cnf(c_0_91,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk7_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_23])).

cnf(c_0_93,negated_conjecture,
    ( ~ v1_xboole_0(k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0) = k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_78]),c_0_88]),c_0_52]),c_0_53]),c_0_79]),c_0_80])]),c_0_56])).

cnf(c_0_95,negated_conjecture,
    ( v1_xboole_0(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0) = esk8_0
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)
    | ~ m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_65])])).

cnf(c_0_97,negated_conjecture,
    ( esk9_0 = esk7_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_51]),c_0_78]),c_0_54]),c_0_79]),c_0_55]),c_0_80])])).

cnf(c_0_98,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94]),c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0) = esk8_0
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_75])])).

cnf(c_0_100,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)
    | ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_94])).

cnf(c_0_101,negated_conjecture,
    ( esk9_0 = esk7_0 ),
    inference(sr,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0) = esk8_0
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_99,c_0_94])).

cnf(c_0_103,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101])])).

cnf(c_0_104,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0) = esk8_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_101]),c_0_103])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:07:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.15/1.38  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 1.15/1.38  # and selection function SelectCQIPrecWNTNp.
% 1.15/1.38  #
% 1.15/1.38  # Preprocessing time       : 0.046 s
% 1.15/1.38  # Presaturation interreduction done
% 1.15/1.38  
% 1.15/1.38  # Proof found!
% 1.15/1.38  # SZS status Theorem
% 1.15/1.38  # SZS output start CNFRefutation
% 1.15/1.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.15/1.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.15/1.38  fof(t80_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tmap_1)).
% 1.15/1.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.15/1.38  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 1.15/1.38  fof(dt_k3_tmap_1, axiom, ![X1, X2, X3, X4, X5]:(((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&m1_pre_topc(X3,X1))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))&v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 1.15/1.38  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 1.15/1.38  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 1.15/1.38  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 1.15/1.38  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 1.15/1.38  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 1.15/1.38  fof(c_0_11, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 1.15/1.38  fof(c_0_12, plain, ![X12, X13, X14, X15, X16]:((~r1_tarski(X12,X13)|(~r2_hidden(X14,X12)|r2_hidden(X14,X13)))&((r2_hidden(esk2_2(X15,X16),X15)|r1_tarski(X15,X16))&(~r2_hidden(esk2_2(X15,X16),X16)|r1_tarski(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.15/1.38  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6))))))))))), inference(assume_negation,[status(cth)],[t80_tmap_1])).
% 1.15/1.38  fof(c_0_14, plain, ![X18, X19]:(((r1_tarski(X18,X19)|X18!=X19)&(r1_tarski(X19,X18)|X18!=X19))&(~r1_tarski(X18,X19)|~r1_tarski(X19,X18)|X18=X19)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.15/1.38  cnf(c_0_15, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.15/1.38  cnf(c_0_16, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.15/1.38  fof(c_0_17, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk3_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk3_0))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,u1_struct_0(esk6_0),u1_struct_0(esk4_0)))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0)))))&((esk6_0=esk3_0&r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0),u1_struct_0(esk4_0),esk7_0,esk9_0))&((~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0))&(r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 1.15/1.38  cnf(c_0_18, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.15/1.38  cnf(c_0_19, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 1.15/1.38  fof(c_0_20, plain, ![X30, X31, X32, X33]:((~r2_funct_2(X30,X31,X32,X33)|X32=X33|(~v1_funct_1(X32)|~v1_funct_2(X32,X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(X32!=X33|r2_funct_2(X30,X31,X32,X33)|(~v1_funct_1(X32)|~v1_funct_2(X32,X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 1.15/1.38  fof(c_0_21, plain, ![X49, X50, X51, X52, X53]:(((v1_funct_1(k3_tmap_1(X49,X50,X51,X52,X53))|(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49)|v2_struct_0(X50)|~v2_pre_topc(X50)|~l1_pre_topc(X50)|~m1_pre_topc(X51,X49)|~m1_pre_topc(X52,X49)|~v1_funct_1(X53)|~v1_funct_2(X53,u1_struct_0(X51),u1_struct_0(X50))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X50))))))&(v1_funct_2(k3_tmap_1(X49,X50,X51,X52,X53),u1_struct_0(X52),u1_struct_0(X50))|(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49)|v2_struct_0(X50)|~v2_pre_topc(X50)|~l1_pre_topc(X50)|~m1_pre_topc(X51,X49)|~m1_pre_topc(X52,X49)|~v1_funct_1(X53)|~v1_funct_2(X53,u1_struct_0(X51),u1_struct_0(X50))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X50)))))))&(m1_subset_1(k3_tmap_1(X49,X50,X51,X52,X53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X50))))|(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49)|v2_struct_0(X50)|~v2_pre_topc(X50)|~l1_pre_topc(X50)|~m1_pre_topc(X51,X49)|~m1_pre_topc(X52,X49)|~v1_funct_1(X53)|~v1_funct_2(X53,u1_struct_0(X51),u1_struct_0(X50))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X50))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).
% 1.15/1.38  cnf(c_0_22, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_23, negated_conjecture, (esk6_0=esk3_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_24, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.15/1.38  cnf(c_0_25, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.15/1.38  cnf(c_0_26, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.15/1.38  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk6_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_32, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.15/1.38  cnf(c_0_33, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 1.15/1.38  cnf(c_0_34, plain, (X1=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_24, c_0_19])).
% 1.15/1.38  cnf(c_0_35, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_25])).
% 1.15/1.38  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_39, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(esk3_0,X1,X2,esk5_0,X3),u1_struct_0(esk5_0),u1_struct_0(X1))|~m1_pre_topc(X2,esk3_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 1.15/1.38  cnf(c_0_40, negated_conjecture, (m1_pre_topc(esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_31, c_0_23])).
% 1.15/1.38  cnf(c_0_41, negated_conjecture, (v1_funct_2(esk9_0,u1_struct_0(esk6_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_43, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(esk3_0,X1,X2,esk5_0,X3))|~m1_pre_topc(X2,esk3_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 1.15/1.38  cnf(c_0_44, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.15/1.38  fof(c_0_45, plain, ![X44, X45, X46, X47, X48]:(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)|(~m1_pre_topc(X46,X44)|(~m1_pre_topc(X47,X44)|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45))))|(~m1_pre_topc(X47,X46)|k3_tmap_1(X44,X45,X46,X47,X48)=k2_partfun1(u1_struct_0(X46),u1_struct_0(X45),X48,u1_struct_0(X47)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 1.15/1.38  fof(c_0_46, plain, ![X54, X55, X56]:(~v2_pre_topc(X54)|~l1_pre_topc(X54)|(~m1_pre_topc(X55,X54)|(~m1_pre_topc(X56,X55)|m1_pre_topc(X56,X54)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 1.15/1.38  cnf(c_0_47, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),X1,esk8_0)|~v1_xboole_0(k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.15/1.38  cnf(c_0_48, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])])).
% 1.15/1.38  fof(c_0_49, plain, ![X27, X28, X29]:(~v1_xboole_0(X27)|(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X27)))|v1_xboole_0(X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 1.15/1.38  cnf(c_0_50, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(esk3_0,X1,esk3_0,esk5_0,X2),u1_struct_0(esk5_0),u1_struct_0(X1))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk3_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.15/1.38  cnf(c_0_51, negated_conjecture, (v1_funct_2(esk9_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_41, c_0_23])).
% 1.15/1.38  cnf(c_0_52, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_53, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_54, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_42, c_0_23])).
% 1.15/1.38  cnf(c_0_56, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_57, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(esk3_0,X1,esk3_0,esk5_0,X2))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk3_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_43, c_0_40])).
% 1.15/1.38  cnf(c_0_58, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(esk3_0,X1,X2,esk5_0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~m1_pre_topc(X2,esk3_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 1.15/1.38  cnf(c_0_59, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.15/1.38  cnf(c_0_60, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.15/1.38  fof(c_0_61, plain, ![X40, X41, X42, X43]:(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X41))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X41))))|(~m1_pre_topc(X43,X40)|k2_tmap_1(X40,X41,X42,X43)=k2_partfun1(u1_struct_0(X40),u1_struct_0(X41),X42,u1_struct_0(X43)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 1.15/1.38  cnf(c_0_62, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_63, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)|~v1_xboole_0(k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0))|~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 1.15/1.38  cnf(c_0_64, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.15/1.38  cnf(c_0_65, negated_conjecture, (v1_funct_2(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53]), c_0_54]), c_0_55])]), c_0_56])).
% 1.15/1.38  cnf(c_0_66, negated_conjecture, (v1_funct_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_51]), c_0_52]), c_0_53]), c_0_54]), c_0_55])]), c_0_56])).
% 1.15/1.38  cnf(c_0_67, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(esk3_0,X1,esk3_0,esk5_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk3_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_58, c_0_40])).
% 1.15/1.38  cnf(c_0_68, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_59, c_0_60])).
% 1.15/1.38  cnf(c_0_69, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.15/1.38  cnf(c_0_70, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.15/1.38  cnf(c_0_71, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(rw,[status(thm)],[c_0_62, c_0_23])).
% 1.15/1.38  cnf(c_0_72, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),X1)|~v1_xboole_0(k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0))|~v1_xboole_0(esk8_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_63, c_0_34])).
% 1.15/1.38  cnf(c_0_73, negated_conjecture, (v1_xboole_0(esk8_0)|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_64, c_0_38])).
% 1.15/1.38  cnf(c_0_74, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0))|~m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_65]), c_0_66])])).
% 1.15/1.38  cnf(c_0_75, negated_conjecture, (m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_51]), c_0_52]), c_0_53]), c_0_54]), c_0_55])]), c_0_56])).
% 1.15/1.38  cnf(c_0_76, negated_conjecture, (k3_tmap_1(X1,X2,esk3_0,esk5_0,X3)=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(X2),X3,u1_struct_0(esk5_0))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~v1_funct_2(X3,u1_struct_0(esk3_0),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X2))))), inference(spm,[status(thm)],[c_0_68, c_0_27])).
% 1.15/1.38  cnf(c_0_77, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(X1),X2,u1_struct_0(esk5_0))=k2_tmap_1(esk3_0,X1,X2,esk5_0)|v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk3_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 1.15/1.38  cnf(c_0_78, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_79, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_81, negated_conjecture, (k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0)=esk8_0|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)|~v1_funct_2(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))|~v1_funct_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0))|~m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_36]), c_0_37]), c_0_38])])).
% 1.15/1.38  fof(c_0_82, plain, ![X34, X35, X36, X37, X38, X39]:((~r1_funct_2(X34,X35,X36,X37,X38,X39)|X38=X39|(v1_xboole_0(X35)|v1_xboole_0(X37)|~v1_funct_1(X38)|~v1_funct_2(X38,X34,X35)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~v1_funct_1(X39)|~v1_funct_2(X39,X36,X37)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))&(X38!=X39|r1_funct_2(X34,X35,X36,X37,X38,X39)|(v1_xboole_0(X35)|v1_xboole_0(X37)|~v1_funct_1(X38)|~v1_funct_2(X38,X34,X35)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~v1_funct_1(X39)|~v1_funct_2(X39,X36,X37)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 1.15/1.38  cnf(c_0_83, negated_conjecture, (r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0),u1_struct_0(esk4_0),esk7_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.38  cnf(c_0_84, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),X1,k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),X2)|~v1_xboole_0(k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0))|~v1_xboole_0(u1_struct_0(esk4_0))|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_34]), c_0_73])).
% 1.15/1.38  cnf(c_0_85, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75])])).
% 1.15/1.38  cnf(c_0_86, negated_conjecture, (v1_xboole_0(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_64, c_0_75])).
% 1.15/1.38  cnf(c_0_87, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(X1),X2,u1_struct_0(esk5_0))=k3_tmap_1(esk3_0,X1,esk3_0,esk5_0,X2)|v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk3_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 1.15/1.38  cnf(c_0_88, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk7_0,u1_struct_0(esk5_0))=k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_52]), c_0_53]), c_0_79]), c_0_80])]), c_0_56])).
% 1.15/1.38  cnf(c_0_89, negated_conjecture, (m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_78]), c_0_52]), c_0_53]), c_0_79]), c_0_80])]), c_0_56])).
% 1.15/1.38  cnf(c_0_90, negated_conjecture, (k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0)=esk8_0|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)|~v1_funct_2(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))|~m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_66])])).
% 1.15/1.38  cnf(c_0_91, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 1.15/1.38  cnf(c_0_92, negated_conjecture, (r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk7_0,esk9_0)), inference(rw,[status(thm)],[c_0_83, c_0_23])).
% 1.15/1.38  cnf(c_0_93, negated_conjecture, (~v1_xboole_0(k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])).
% 1.15/1.38  cnf(c_0_94, negated_conjecture, (k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0)=k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_78]), c_0_88]), c_0_52]), c_0_53]), c_0_79]), c_0_80])]), c_0_56])).
% 1.15/1.38  cnf(c_0_95, negated_conjecture, (v1_xboole_0(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_64, c_0_89])).
% 1.15/1.38  cnf(c_0_96, negated_conjecture, (k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0)=esk8_0|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)|~m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_65])])).
% 1.15/1.38  cnf(c_0_97, negated_conjecture, (esk9_0=esk7_0|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_51]), c_0_78]), c_0_54]), c_0_79]), c_0_55]), c_0_80])])).
% 1.15/1.38  cnf(c_0_98, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94]), c_0_95])).
% 1.15/1.38  cnf(c_0_99, negated_conjecture, (k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0)=esk8_0|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_75])])).
% 1.15/1.38  cnf(c_0_100, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0),esk8_0)), inference(rw,[status(thm)],[c_0_33, c_0_94])).
% 1.15/1.38  cnf(c_0_101, negated_conjecture, (esk9_0=esk7_0), inference(sr,[status(thm)],[c_0_97, c_0_98])).
% 1.15/1.38  cnf(c_0_102, negated_conjecture, (k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0)=esk8_0|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0),esk8_0)), inference(rw,[status(thm)],[c_0_99, c_0_94])).
% 1.15/1.38  cnf(c_0_103, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_101])])).
% 1.15/1.38  cnf(c_0_104, negated_conjecture, (k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0)=esk8_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_101]), c_0_103])).
% 1.15/1.38  cnf(c_0_105, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104]), c_0_48])]), ['proof']).
% 1.15/1.38  # SZS output end CNFRefutation
% 1.15/1.38  # Proof object total steps             : 106
% 1.15/1.38  # Proof object clause steps            : 83
% 1.15/1.38  # Proof object formula steps           : 23
% 1.15/1.38  # Proof object conjectures             : 68
% 1.15/1.38  # Proof object clause conjectures      : 65
% 1.15/1.38  # Proof object formula conjectures     : 3
% 1.15/1.38  # Proof object initial clauses used    : 34
% 1.15/1.38  # Proof object initial formulas used   : 11
% 1.15/1.38  # Proof object generating inferences   : 30
% 1.15/1.38  # Proof object simplifying inferences  : 103
% 1.15/1.38  # Training examples: 0 positive, 0 negative
% 1.15/1.38  # Parsed axioms                        : 15
% 1.15/1.38  # Removed by relevancy pruning/SinE    : 0
% 1.15/1.38  # Initial clauses                      : 46
% 1.15/1.38  # Removed in clause preprocessing      : 1
% 1.15/1.38  # Initial clauses in saturation        : 45
% 1.15/1.38  # Processed clauses                    : 7891
% 1.15/1.38  # ...of these trivial                  : 30
% 1.15/1.38  # ...subsumed                          : 5604
% 1.15/1.38  # ...remaining for further processing  : 2257
% 1.15/1.38  # Other redundant clauses eliminated   : 4
% 1.15/1.38  # Clauses deleted for lack of memory   : 0
% 1.15/1.38  # Backward-subsumed                    : 140
% 1.15/1.38  # Backward-rewritten                   : 987
% 1.15/1.38  # Generated clauses                    : 47095
% 1.15/1.38  # ...of the previous two non-trivial   : 47714
% 1.15/1.38  # Contextual simplify-reflections      : 37
% 1.15/1.38  # Paramodulations                      : 47087
% 1.15/1.38  # Factorizations                       : 0
% 1.15/1.38  # Equation resolutions                 : 4
% 1.15/1.38  # Propositional unsat checks           : 0
% 1.15/1.38  #    Propositional check models        : 0
% 1.15/1.38  #    Propositional check unsatisfiable : 0
% 1.15/1.38  #    Propositional clauses             : 0
% 1.15/1.38  #    Propositional clauses after purity: 0
% 1.15/1.38  #    Propositional unsat core size     : 0
% 1.15/1.38  #    Propositional preprocessing time  : 0.000
% 1.15/1.38  #    Propositional encoding time       : 0.000
% 1.15/1.38  #    Propositional solver time         : 0.000
% 1.15/1.38  #    Success case prop preproc time    : 0.000
% 1.15/1.38  #    Success case prop encoding time   : 0.000
% 1.15/1.38  #    Success case prop solver time     : 0.000
% 1.15/1.38  # Current number of processed clauses  : 1079
% 1.15/1.38  #    Positive orientable unit clauses  : 65
% 1.15/1.38  #    Positive unorientable unit clauses: 0
% 1.15/1.38  #    Negative unit clauses             : 5
% 1.15/1.38  #    Non-unit-clauses                  : 1009
% 1.15/1.38  # Current number of unprocessed clauses: 39774
% 1.15/1.38  # ...number of literals in the above   : 230365
% 1.15/1.38  # Current number of archived formulas  : 0
% 1.15/1.38  # Current number of archived clauses   : 1175
% 1.15/1.38  # Clause-clause subsumption calls (NU) : 1307545
% 1.15/1.38  # Rec. Clause-clause subsumption calls : 68221
% 1.15/1.38  # Non-unit clause-clause subsumptions  : 5761
% 1.15/1.38  # Unit Clause-clause subsumption calls : 3485
% 1.15/1.38  # Rewrite failures with RHS unbound    : 0
% 1.15/1.38  # BW rewrite match attempts            : 3441
% 1.15/1.38  # BW rewrite match successes           : 16
% 1.15/1.38  # Condensation attempts                : 0
% 1.15/1.38  # Condensation successes               : 0
% 1.15/1.38  # Termbank termtop insertions          : 1192597
% 1.22/1.38  
% 1.22/1.38  # -------------------------------------------------
% 1.22/1.38  # User time                : 1.008 s
% 1.22/1.38  # System time              : 0.026 s
% 1.22/1.38  # Total time               : 1.034 s
% 1.22/1.38  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
