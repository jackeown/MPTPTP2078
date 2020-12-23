%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:44 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 446 expanded)
%              Number of clauses        :   50 ( 149 expanded)
%              Number of leaves         :   11 ( 105 expanded)
%              Depth                    :   14
%              Number of atoms          :  335 (6819 expanded)
%              Number of equality atoms :   26 ( 327 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

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

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(rc7_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2)
          & v4_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    ! [X30,X31,X32,X33,X34] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | ~ m1_pre_topc(X32,X30)
      | ~ m1_pre_topc(X33,X30)
      | ~ v1_funct_1(X34)
      | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X31))
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))
      | ~ m1_pre_topc(X33,X32)
      | k3_tmap_1(X30,X31,X32,X33,X34) = k2_partfun1(u1_struct_0(X32),u1_struct_0(X31),X34,u1_struct_0(X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_14,plain,(
    ! [X36,X37,X38] :
      ( ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_pre_topc(X37,X36)
      | ~ m1_pre_topc(X38,X37)
      | m1_pre_topc(X38,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_15,plain,(
    ! [X26,X27,X28,X29] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | ~ v1_funct_1(X28)
      | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))
      | ~ m1_pre_topc(X29,X26)
      | k2_tmap_1(X26,X27,X28,X29) = k2_partfun1(u1_struct_0(X26),u1_struct_0(X27),X28,u1_struct_0(X29)) ) ),
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

fof(c_0_36,plain,(
    ! [X35] :
      ( ~ l1_pre_topc(X35)
      | m1_pre_topc(X35,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_37,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r1_funct_2(X20,X21,X22,X23,X24,X25)
        | X24 = X25
        | v1_xboole_0(X21)
        | v1_xboole_0(X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X20,X21)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X22,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( X24 != X25
        | r1_funct_2(X20,X21,X22,X23,X24,X25)
        | v1_xboole_0(X21)
        | v1_xboole_0(X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X20,X21)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X22,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_38,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0),u1_struct_0(esk4_0),esk7_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)
    | ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( k3_tmap_1(X1,esk4_0,esk3_0,esk5_0,esk9_0) = k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_35])).

cnf(c_0_41,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_42,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | ~ v1_xboole_0(X17) ) ),
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

cnf(c_0_45,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk7_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)
    | ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0) = k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_25]),c_0_27])]),c_0_30])).

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
    ! [X18] :
      ( ( m1_subset_1(esk2_1(X18),k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ v1_xboole_0(esk2_1(X18))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( v4_pre_topc(esk2_1(X18),X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).

cnf(c_0_55,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_17])).

cnf(c_0_56,negated_conjecture,
    ( esk9_0 = esk7_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_22]),c_0_47]),c_0_23]),c_0_48]),c_0_28]),c_0_49])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0),esk8_0)
    | ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0),esk8_0)
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0) = k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_56])).

fof(c_0_63,plain,(
    ! [X14] :
      ( ~ r1_tarski(X14,k1_xboole_0)
      | X14 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | r1_tarski(esk2_1(X1),X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk2_1(esk4_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk2_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_69,negated_conjecture,
    ( esk2_1(esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_24]),c_0_26]),c_0_70])]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.20/0.38  # and selection function SelectCQIPrecWNTNp.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t80_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_tmap_1)).
% 0.20/0.38  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.20/0.38  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.20/0.38  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.20/0.38  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.20/0.38  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.20/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(rc7_pre_topc, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>?[X2]:((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v4_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 0.20/0.38  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.20/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6))))))))))), inference(assume_negation,[status(cth)],[t80_tmap_1])).
% 0.20/0.38  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk3_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk3_0))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,u1_struct_0(esk6_0),u1_struct_0(esk4_0)))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0)))))&((esk6_0=esk3_0&r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0),u1_struct_0(esk4_0),esk7_0,esk9_0))&((~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0))&(r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.20/0.38  fof(c_0_13, plain, ![X30, X31, X32, X33, X34]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(~m1_pre_topc(X32,X30)|(~m1_pre_topc(X33,X30)|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X31))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))|(~m1_pre_topc(X33,X32)|k3_tmap_1(X30,X31,X32,X33,X34)=k2_partfun1(u1_struct_0(X32),u1_struct_0(X31),X34,u1_struct_0(X33)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.20/0.38  fof(c_0_14, plain, ![X36, X37, X38]:(~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~m1_pre_topc(X37,X36)|(~m1_pre_topc(X38,X37)|m1_pre_topc(X38,X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.20/0.38  fof(c_0_15, plain, ![X26, X27, X28, X29]:(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(~v1_funct_1(X28)|~v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))|(~m1_pre_topc(X29,X26)|k2_tmap_1(X26,X27,X28,X29)=k2_partfun1(u1_struct_0(X26),u1_struct_0(X27),X28,u1_struct_0(X29)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (v1_funct_2(esk9_0,u1_struct_0(esk6_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (esk6_0=esk3_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_19, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_20, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_21, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk9_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_31, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk9_0,u1_struct_0(X1))=k2_tmap_1(esk3_0,esk4_0,esk9_0,X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_30])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (k3_tmap_1(X1,esk4_0,esk3_0,X2,esk9_0)=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk9_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_22]), c_0_23]), c_0_24]), c_0_26]), c_0_28])]), c_0_29])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk9_0,u1_struct_0(esk5_0))=k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.38  fof(c_0_36, plain, ![X35]:(~l1_pre_topc(X35)|m1_pre_topc(X35,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.20/0.38  fof(c_0_37, plain, ![X20, X21, X22, X23, X24, X25]:((~r1_funct_2(X20,X21,X22,X23,X24,X25)|X24=X25|(v1_xboole_0(X21)|v1_xboole_0(X23)|~v1_funct_1(X24)|~v1_funct_2(X24,X20,X21)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~v1_funct_1(X25)|~v1_funct_2(X25,X22,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))&(X24!=X25|r1_funct_2(X20,X21,X22,X23,X24,X25)|(v1_xboole_0(X21)|v1_xboole_0(X23)|~v1_funct_1(X24)|~v1_funct_2(X24,X20,X21)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~v1_funct_1(X25)|~v1_funct_2(X25,X22,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0),u1_struct_0(esk4_0),esk7_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (k3_tmap_1(X1,esk4_0,esk3_0,esk5_0,esk9_0)=k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0)|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_35])).
% 0.20/0.38  cnf(c_0_41, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.38  fof(c_0_42, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|~v1_xboole_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.38  fof(c_0_43, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk9_0),esk8_0)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_45, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk7_0,esk9_0)), inference(rw,[status(thm)],[c_0_38, c_0_17])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(rw,[status(thm)],[c_0_39, c_0_17])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0)=k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_25]), c_0_27])]), c_0_30])).
% 0.20/0.38  cnf(c_0_52, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.38  cnf(c_0_53, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.38  fof(c_0_54, plain, ![X18]:(((m1_subset_1(esk2_1(X18),k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(~v1_xboole_0(esk2_1(X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18))))&(v4_pre_topc(esk2_1(X18),X18)|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk9_0),esk8_0)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(rw,[status(thm)],[c_0_44, c_0_17])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (esk9_0=esk7_0|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_22]), c_0_47]), c_0_23]), c_0_48]), c_0_28]), c_0_49])])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk9_0,esk5_0),esk8_0)|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.38  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.38  cnf(c_0_59, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0),esk8_0)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (k3_tmap_1(esk3_0,esk4_0,esk3_0,esk5_0,esk7_0)=k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_56])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tmap_1(esk3_0,esk4_0,esk7_0,esk5_0),esk8_0)), inference(spm,[status(thm)],[c_0_57, c_0_56])).
% 0.20/0.38  fof(c_0_63, plain, ![X14]:(~r1_tarski(X14,k1_xboole_0)|X14=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.20/0.38  cnf(c_0_64, plain, (v2_struct_0(X1)|r1_tarski(esk2_1(X1),X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.20/0.38  cnf(c_0_66, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.38  cnf(c_0_67, negated_conjecture, (r1_tarski(esk2_1(esk4_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_24]), c_0_26])]), c_0_29])).
% 0.20/0.38  cnf(c_0_68, plain, (v2_struct_0(X1)|~v1_xboole_0(esk2_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.38  cnf(c_0_69, negated_conjecture, (esk2_1(esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.38  cnf(c_0_70, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.38  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_24]), c_0_26]), c_0_70])]), c_0_29]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 72
% 0.20/0.38  # Proof object clause steps            : 50
% 0.20/0.38  # Proof object formula steps           : 22
% 0.20/0.38  # Proof object conjectures             : 39
% 0.20/0.38  # Proof object clause conjectures      : 36
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 28
% 0.20/0.38  # Proof object initial formulas used   : 11
% 0.20/0.38  # Proof object generating inferences   : 15
% 0.20/0.38  # Proof object simplifying inferences  : 44
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 11
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 38
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 38
% 0.20/0.38  # Processed clauses                    : 118
% 0.20/0.38  # ...of these trivial                  : 5
% 0.20/0.38  # ...subsumed                          : 4
% 0.20/0.38  # ...remaining for further processing  : 109
% 0.20/0.38  # Other redundant clauses eliminated   : 1
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 13
% 0.20/0.38  # Generated clauses                    : 60
% 0.20/0.38  # ...of the previous two non-trivial   : 52
% 0.20/0.38  # Contextual simplify-reflections      : 2
% 0.20/0.38  # Paramodulations                      : 59
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 1
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 58
% 0.20/0.38  #    Positive orientable unit clauses  : 26
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 3
% 0.20/0.38  #    Non-unit-clauses                  : 29
% 0.20/0.38  # Current number of unprocessed clauses: 6
% 0.20/0.38  # ...number of literals in the above   : 26
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 50
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 1185
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 160
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.20/0.38  # Unit Clause-clause subsumption calls : 37
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 21
% 0.20/0.38  # BW rewrite match successes           : 3
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 5395
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.035 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.039 s
% 0.20/0.38  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
