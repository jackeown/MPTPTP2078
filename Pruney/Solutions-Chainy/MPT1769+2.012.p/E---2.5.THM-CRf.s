%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:43 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 414 expanded)
%              Number of clauses        :   52 ( 139 expanded)
%              Number of leaves         :   11 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  340 (6341 expanded)
%              Number of equality atoms :   28 ( 305 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   25 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(rc7_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2)
          & v4_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_13,plain,(
    ! [X32,X33,X34,X35,X36] :
      ( v2_struct_0(X32)
      | ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ m1_pre_topc(X34,X32)
      | ~ m1_pre_topc(X35,X32)
      | ~ v1_funct_1(X36)
      | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X33))
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X33))))
      | ~ m1_pre_topc(X35,X34)
      | k3_tmap_1(X32,X33,X34,X35,X36) = k2_partfun1(u1_struct_0(X34),u1_struct_0(X33),X36,u1_struct_0(X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_14,plain,(
    ! [X37,X38,X39] :
      ( ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | ~ m1_pre_topc(X38,X37)
      | ~ m1_pre_topc(X39,X38)
      | m1_pre_topc(X39,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_15,plain,(
    ! [X28,X29,X30,X31] :
      ( v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | ~ v1_funct_1(X30)
      | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
      | ~ m1_pre_topc(X31,X28)
      | k2_tmap_1(X28,X29,X30,X31) = k2_partfun1(u1_struct_0(X28),u1_struct_0(X29),X30,u1_struct_0(X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_2(esk9_0,u1_struct_0(esk6_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk6_0 = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
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

cnf(c_0_20,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk9_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk9_0,u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk4_0,esk9_0,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( k3_tmap_1(X1,esk4_0,esk3_0,X2,esk9_0) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk9_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_22]),c_0_23]),c_0_24]),c_0_26]),c_0_28])]),c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk9_0,u1_struct_0(esk5_0)) = k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)
    | ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( k3_tmap_1(X1,esk4_0,esk3_0,esk5_0,esk9_0) = k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_17])).

fof(c_0_40,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( ~ r1_funct_2(X22,X23,X24,X25,X26,X27)
        | X26 = X27
        | v1_xboole_0(X23)
        | v1_xboole_0(X25)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X22,X23)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X24,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( X26 != X27
        | r1_funct_2(X22,X23,X24,X25,X26,X27)
        | v1_xboole_0(X23)
        | v1_xboole_0(X25)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X22,X23)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X24,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_41,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0),u1_struct_0(esk4_0),esk7_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_42,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | ~ v1_xboole_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_43,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_44,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)
    | ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0) = k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_25]),c_0_27])]),c_0_30])).

cnf(c_0_47,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk7_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_54,plain,(
    ! [X20] :
      ( ( m1_subset_1(esk2_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ v1_xboole_0(esk2_1(X20))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( v4_pre_topc(esk2_1(X20),X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).

cnf(c_0_55,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_17])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0),esk8_0)
    | ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( esk9_0 = esk7_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_22]),c_0_49]),c_0_23]),c_0_50]),c_0_28]),c_0_51])])).

fof(c_0_58,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_59,plain,(
    ! [X16] : r1_tarski(k1_xboole_0,X16) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_46])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | r1_tarski(esk2_1(X1),X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_57]),c_0_63])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk2_1(esk4_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk2_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_71,negated_conjecture,
    ( esk2_1(esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_24]),c_0_26]),c_0_72])]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:17:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.37  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.029 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t80_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tmap_1)).
% 0.13/0.37  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.13/0.37  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.13/0.37  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.13/0.37  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.13/0.37  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.13/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.37  fof(rc7_pre_topc, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>?[X2]:((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v4_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 0.13/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.37  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6))))))))))), inference(assume_negation,[status(cth)],[t80_tmap_1])).
% 0.13/0.37  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk3_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk3_0))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,u1_struct_0(esk6_0),u1_struct_0(esk4_0)))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0)))))&((esk6_0=esk3_0&r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0),u1_struct_0(esk4_0),esk7_0,esk9_0))&((~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0))&(r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.13/0.37  fof(c_0_13, plain, ![X32, X33, X34, X35, X36]:(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|(~m1_pre_topc(X34,X32)|(~m1_pre_topc(X35,X32)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X33))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X33))))|(~m1_pre_topc(X35,X34)|k3_tmap_1(X32,X33,X34,X35,X36)=k2_partfun1(u1_struct_0(X34),u1_struct_0(X33),X36,u1_struct_0(X35)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.13/0.37  fof(c_0_14, plain, ![X37, X38, X39]:(~v2_pre_topc(X37)|~l1_pre_topc(X37)|(~m1_pre_topc(X38,X37)|(~m1_pre_topc(X39,X38)|m1_pre_topc(X39,X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.13/0.37  fof(c_0_15, plain, ![X28, X29, X30, X31]:(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))|(~m1_pre_topc(X31,X28)|k2_tmap_1(X28,X29,X30,X31)=k2_partfun1(u1_struct_0(X28),u1_struct_0(X29),X30,u1_struct_0(X31)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (v1_funct_2(esk9_0,u1_struct_0(esk6_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (esk6_0=esk3_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_19, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_20, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_21, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk9_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_31, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk9_0,u1_struct_0(X1))=k2_tmap_1(esk3_0,esk4_0,esk9_0,X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_30])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (k3_tmap_1(X1,esk4_0,esk3_0,X2,esk9_0)=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk9_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_22]), c_0_23]), c_0_24]), c_0_26]), c_0_28])]), c_0_29])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk9_0,u1_struct_0(esk5_0))=k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (m1_pre_topc(esk6_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (k3_tmap_1(X1,esk4_0,esk3_0,esk5_0,esk9_0)=k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0)|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_35])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (m1_pre_topc(esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_36, c_0_17])).
% 0.13/0.37  fof(c_0_40, plain, ![X22, X23, X24, X25, X26, X27]:((~r1_funct_2(X22,X23,X24,X25,X26,X27)|X26=X27|(v1_xboole_0(X23)|v1_xboole_0(X25)|~v1_funct_1(X26)|~v1_funct_2(X26,X22,X23)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|~v1_funct_1(X27)|~v1_funct_2(X27,X24,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))&(X26!=X27|r1_funct_2(X22,X23,X24,X25,X26,X27)|(v1_xboole_0(X23)|v1_xboole_0(X25)|~v1_funct_1(X26)|~v1_funct_2(X26,X22,X23)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|~v1_funct_1(X27)|~v1_funct_2(X27,X24,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0),u1_struct_0(esk4_0),esk7_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  fof(c_0_42, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|~v1_xboole_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.13/0.37  fof(c_0_43, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(rw,[status(thm)],[c_0_37, c_0_17])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0)=k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_25]), c_0_27])]), c_0_30])).
% 0.13/0.37  cnf(c_0_47, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, (r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk7_0,esk9_0)), inference(rw,[status(thm)],[c_0_41, c_0_17])).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_52, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.37  cnf(c_0_53, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.37  fof(c_0_54, plain, ![X20]:(((m1_subset_1(esk2_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~v1_xboole_0(esk2_1(X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))))&(v4_pre_topc(esk2_1(X20),X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).
% 0.13/0.37  cnf(c_0_55, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(rw,[status(thm)],[c_0_44, c_0_17])).
% 0.13/0.37  cnf(c_0_56, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0),esk8_0)|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.37  cnf(c_0_57, negated_conjecture, (esk9_0=esk7_0|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_22]), c_0_49]), c_0_23]), c_0_50]), c_0_28]), c_0_51])])).
% 0.13/0.37  fof(c_0_58, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.37  fof(c_0_59, plain, ![X16]:r1_tarski(k1_xboole_0,X16), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.37  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.37  cnf(c_0_61, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.37  cnf(c_0_62, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0),esk8_0)), inference(rw,[status(thm)],[c_0_55, c_0_46])).
% 0.13/0.37  cnf(c_0_63, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.37  cnf(c_0_64, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.37  cnf(c_0_65, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.37  cnf(c_0_66, plain, (v2_struct_0(X1)|r1_tarski(esk2_1(X1),X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.37  cnf(c_0_67, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_57]), c_0_63])).
% 0.13/0.37  cnf(c_0_68, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.13/0.37  cnf(c_0_69, negated_conjecture, (r1_tarski(esk2_1(esk4_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_24]), c_0_26])]), c_0_29])).
% 0.13/0.37  cnf(c_0_70, plain, (v2_struct_0(X1)|~v1_xboole_0(esk2_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.37  cnf(c_0_71, negated_conjecture, (esk2_1(esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.13/0.37  cnf(c_0_72, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.37  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_24]), c_0_26]), c_0_72])]), c_0_29]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 74
% 0.13/0.37  # Proof object clause steps            : 52
% 0.13/0.37  # Proof object formula steps           : 22
% 0.13/0.37  # Proof object conjectures             : 40
% 0.13/0.37  # Proof object clause conjectures      : 37
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 29
% 0.13/0.37  # Proof object initial formulas used   : 11
% 0.13/0.37  # Proof object generating inferences   : 14
% 0.13/0.37  # Proof object simplifying inferences  : 46
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 11
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 40
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 40
% 0.13/0.37  # Processed clauses                    : 108
% 0.13/0.37  # ...of these trivial                  : 2
% 0.13/0.37  # ...subsumed                          : 1
% 0.13/0.37  # ...remaining for further processing  : 105
% 0.13/0.37  # Other redundant clauses eliminated   : 3
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 7
% 0.13/0.37  # Generated clauses                    : 48
% 0.13/0.37  # ...of the previous two non-trivial   : 40
% 0.13/0.37  # Contextual simplify-reflections      : 2
% 0.13/0.37  # Paramodulations                      : 45
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 3
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 57
% 0.13/0.37  #    Positive orientable unit clauses  : 27
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 3
% 0.13/0.37  #    Non-unit-clauses                  : 27
% 0.13/0.37  # Current number of unprocessed clauses: 9
% 0.13/0.37  # ...number of literals in the above   : 40
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 45
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 993
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 111
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.37  # Unit Clause-clause subsumption calls : 27
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 18
% 0.13/0.37  # BW rewrite match successes           : 3
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 4923
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.036 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.039 s
% 0.13/0.37  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
