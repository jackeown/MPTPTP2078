%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:44 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  105 (9121 expanded)
%              Number of clauses        :   82 (3113 expanded)
%              Number of leaves         :   11 (2108 expanded)
%              Depth                    :   17
%              Number of atoms          :  394 (138679 expanded)
%              Number of equality atoms :   42 (6804 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal clause size      :   25 (   2 average)
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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(fc3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X2)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

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
    & v1_funct_2(esk8_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))
    & v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,u1_struct_0(esk6_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0))))
    & v1_funct_1(esk10_0)
    & v1_funct_2(esk10_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0))))
    & esk7_0 = esk4_0
    & r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,esk10_0)
    & ( ~ r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk10_0),esk9_0)
      | ~ r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0) )
    & ( r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk10_0),esk9_0)
      | r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_13,plain,(
    ! [X43,X44,X45,X46,X47] :
      ( v2_struct_0(X43)
      | ~ v2_pre_topc(X43)
      | ~ l1_pre_topc(X43)
      | v2_struct_0(X44)
      | ~ v2_pre_topc(X44)
      | ~ l1_pre_topc(X44)
      | ~ m1_pre_topc(X45,X43)
      | ~ m1_pre_topc(X46,X43)
      | ~ v1_funct_1(X47)
      | ~ v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X44))
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X44))))
      | ~ m1_pre_topc(X46,X45)
      | k3_tmap_1(X43,X44,X45,X46,X47) = k2_partfun1(u1_struct_0(X45),u1_struct_0(X44),X47,u1_struct_0(X46)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_14,plain,(
    ! [X48,X49,X50] :
      ( ~ v2_pre_topc(X48)
      | ~ l1_pre_topc(X48)
      | ~ m1_pre_topc(X49,X48)
      | ~ m1_pre_topc(X50,X49)
      | m1_pre_topc(X50,X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_15,plain,(
    ! [X39,X40,X41,X42] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | v2_struct_0(X40)
      | ~ v2_pre_topc(X40)
      | ~ l1_pre_topc(X40)
      | ~ v1_funct_1(X41)
      | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
      | ~ m1_pre_topc(X42,X39)
      | k2_tmap_1(X39,X40,X41,X42) = k2_partfun1(u1_struct_0(X39),u1_struct_0(X40),X41,u1_struct_0(X42)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_2(esk10_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk7_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0)))) ),
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
    ( v1_funct_2(esk10_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_31,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X31,k1_zfmisc_1(X32))
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(X31,X32)
        | m1_subset_1(X31,k1_zfmisc_1(X32)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_32,plain,
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
    inference(csr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk10_0,u1_struct_0(X1)) = k2_tmap_1(esk4_0,esk5_0,esk10_0,X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_35,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_tarski(X15,X16) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( k3_tmap_1(X1,esk5_0,esk4_0,X2,esk10_0) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk10_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_22]),c_0_23]),c_0_25]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk10_0,u1_struct_0(esk6_0)) = k2_tmap_1(esk4_0,esk5_0,esk10_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_41,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k2_xboole_0(X27,X28) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk9_0,k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_46,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_47,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ( ~ r1_funct_2(X33,X34,X35,X36,X37,X38)
        | X37 = X38
        | v1_xboole_0(X34)
        | v1_xboole_0(X36)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X33,X34)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X35,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X37 != X38
        | r1_funct_2(X33,X34,X35,X36,X37,X38)
        | v1_xboole_0(X34)
        | v1_xboole_0(X36)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X33,X34)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X35,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_48,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk10_0),esk9_0)
    | ~ r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( k3_tmap_1(X1,esk5_0,esk4_0,esk6_0,esk10_0) = k2_tmap_1(esk4_0,esk5_0,esk10_0,esk6_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_17])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_53,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X21,X20)
        | r2_hidden(X21,X18)
        | r2_hidden(X21,X19)
        | X20 != k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X18)
        | r2_hidden(X22,X20)
        | X20 != k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk3_3(X23,X24,X25),X23)
        | ~ r2_hidden(esk3_3(X23,X24,X25),X25)
        | X25 = k2_xboole_0(X23,X24) )
      & ( ~ r2_hidden(esk3_3(X23,X24,X25),X24)
        | ~ r2_hidden(esk3_3(X23,X24,X25),X25)
        | X25 = k2_xboole_0(X23,X24) )
      & ( r2_hidden(esk3_3(X23,X24,X25),X25)
        | r2_hidden(esk3_3(X23,X24,X25),X23)
        | r2_hidden(esk3_3(X23,X24,X25),X24)
        | X25 = k2_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0)))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk10_0),esk9_0)
    | r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_59,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk8_0,esk10_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_17])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k3_tmap_1(esk4_0,esk5_0,esk4_0,esk6_0,esk10_0),esk9_0)
    | ~ r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_17])).

cnf(c_0_64,negated_conjecture,
    ( k3_tmap_1(esk4_0,esk5_0,esk4_0,esk6_0,esk10_0) = k2_tmap_1(esk4_0,esk5_0,esk10_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_24]),c_0_26])]),c_0_30])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk10_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_52])).

cnf(c_0_67,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | r2_hidden(esk3_3(X1,X2,X3),X1)
    | r2_hidden(esk3_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_69,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk1_1(esk9_0),k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0)))
    | v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_71,plain,(
    ! [X29,X30] :
      ( ~ v1_xboole_0(X30)
      | v1_xboole_0(k2_zfmisc_1(X29,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).

cnf(c_0_72,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k3_tmap_1(esk4_0,esk5_0,esk4_0,esk6_0,esk10_0),esk9_0)
    | r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_17])).

cnf(c_0_73,negated_conjecture,
    ( esk10_0 = esk8_0
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_22]),c_0_61]),c_0_27]),c_0_62]),c_0_28]),c_0_52])])).

cnf(c_0_74,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk10_0,esk6_0),esk9_0)
    | ~ r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_66])).

cnf(c_0_77,plain,
    ( X1 = X2
    | r2_hidden(esk3_3(X2,X2,X1),X2)
    | r2_hidden(esk3_3(X2,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_67]),c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_79,plain,
    ( v1_xboole_0(k2_zfmisc_1(X2,X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_80,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k3_tmap_1(esk4_0,esk5_0,esk4_0,esk6_0,esk8_0),esk9_0)
    | r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( k3_tmap_1(esk4_0,esk5_0,esk4_0,esk6_0,esk8_0) = k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk1_1(esk10_0),k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))
    | v1_xboole_0(esk10_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_57])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk1_1(esk8_0),k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))
    | v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_57])).

cnf(c_0_85,plain,
    ( X1 = X2
    | r2_hidden(esk3_3(X2,X2,X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(esk10_0)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_84])).

cnf(c_0_90,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_92,negated_conjecture,
    ( v1_xboole_0(esk10_0)
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_79])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_79])).

cnf(c_0_94,negated_conjecture,
    ( esk9_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( v1_xboole_0(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_87])])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_87])])).

cnf(c_0_97,negated_conjecture,
    ( esk10_0 = esk9_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( esk8_0 = esk9_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_96])).

cnf(c_0_99,negated_conjecture,
    ( u1_struct_0(esk5_0) = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_87])).

cnf(c_0_100,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk9_0,esk6_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_97]),c_0_98])])).

cnf(c_0_101,negated_conjecture,
    ( esk9_0 = u1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_91])).

cnf(c_0_102,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0)
    | r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk10_0,esk6_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_72,c_0_64])).

cnf(c_0_103,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101]),c_0_101])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_97]),c_0_98]),c_0_101]),c_0_101]),c_0_101]),c_0_101])]),c_0_103]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:38:16 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.51  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.18/0.51  # and selection function SelectCQIPrecWNTNp.
% 0.18/0.51  #
% 0.18/0.51  # Preprocessing time       : 0.029 s
% 0.18/0.51  # Presaturation interreduction done
% 0.18/0.51  
% 0.18/0.51  # Proof found!
% 0.18/0.51  # SZS status Theorem
% 0.18/0.51  # SZS output start CNFRefutation
% 0.18/0.51  fof(t80_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_tmap_1)).
% 0.18/0.51  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.18/0.51  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.18/0.51  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.18/0.51  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.51  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.51  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.18/0.51  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.18/0.51  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.18/0.51  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.18/0.51  fof(fc3_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X2)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 0.18/0.51  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6))))))))))), inference(assume_negation,[status(cth)],[t80_tmap_1])).
% 0.18/0.51  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk4_0))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk4_0))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,u1_struct_0(esk6_0),u1_struct_0(esk5_0)))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0)))))&(((v1_funct_1(esk10_0)&v1_funct_2(esk10_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0)))&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0)))))&((esk7_0=esk4_0&r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,esk10_0))&((~r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk10_0),esk9_0)|~r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0))&(r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk10_0),esk9_0)|r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.18/0.51  fof(c_0_13, plain, ![X43, X44, X45, X46, X47]:(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|(~m1_pre_topc(X45,X43)|(~m1_pre_topc(X46,X43)|(~v1_funct_1(X47)|~v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X44))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X44))))|(~m1_pre_topc(X46,X45)|k3_tmap_1(X43,X44,X45,X46,X47)=k2_partfun1(u1_struct_0(X45),u1_struct_0(X44),X47,u1_struct_0(X46)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.18/0.51  fof(c_0_14, plain, ![X48, X49, X50]:(~v2_pre_topc(X48)|~l1_pre_topc(X48)|(~m1_pre_topc(X49,X48)|(~m1_pre_topc(X50,X49)|m1_pre_topc(X50,X48)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.18/0.51  fof(c_0_15, plain, ![X39, X40, X41, X42]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))|(~m1_pre_topc(X42,X39)|k2_tmap_1(X39,X40,X41,X42)=k2_partfun1(u1_struct_0(X39),u1_struct_0(X40),X41,u1_struct_0(X42)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.18/0.51  cnf(c_0_16, negated_conjecture, (v1_funct_2(esk10_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  cnf(c_0_17, negated_conjecture, (esk7_0=esk4_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  cnf(c_0_19, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.51  cnf(c_0_20, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.51  cnf(c_0_21, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.51  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk10_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.51  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 0.18/0.51  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  fof(c_0_31, plain, ![X31, X32]:((~m1_subset_1(X31,k1_zfmisc_1(X32))|r1_tarski(X31,X32))&(~r1_tarski(X31,X32)|m1_subset_1(X31,k1_zfmisc_1(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.51  cnf(c_0_32, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.51  cnf(c_0_33, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk10_0,u1_struct_0(X1))=k2_tmap_1(esk4_0,esk5_0,esk10_0,X1)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_30])).
% 0.18/0.51  cnf(c_0_34, negated_conjecture, (m1_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  fof(c_0_35, plain, ![X12, X13, X14, X15, X16]:((~r1_tarski(X12,X13)|(~r2_hidden(X14,X12)|r2_hidden(X14,X13)))&((r2_hidden(esk2_2(X15,X16),X15)|r1_tarski(X15,X16))&(~r2_hidden(esk2_2(X15,X16),X16)|r1_tarski(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.51  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.51  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  cnf(c_0_38, negated_conjecture, (k3_tmap_1(X1,esk5_0,esk4_0,X2,esk10_0)=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk10_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_22]), c_0_23]), c_0_25]), c_0_27]), c_0_28])]), c_0_29])).
% 0.18/0.51  cnf(c_0_39, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk10_0,u1_struct_0(esk6_0))=k2_tmap_1(esk4_0,esk5_0,esk10_0,esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.51  cnf(c_0_40, negated_conjecture, (m1_pre_topc(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  fof(c_0_41, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k2_xboole_0(X27,X28)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.18/0.51  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.51  cnf(c_0_43, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.51  cnf(c_0_44, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.51  cnf(c_0_45, negated_conjecture, (r1_tarski(esk9_0,k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.51  fof(c_0_46, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.18/0.51  fof(c_0_47, plain, ![X33, X34, X35, X36, X37, X38]:((~r1_funct_2(X33,X34,X35,X36,X37,X38)|X37=X38|(v1_xboole_0(X34)|v1_xboole_0(X36)|~v1_funct_1(X37)|~v1_funct_2(X37,X33,X34)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|~v1_funct_1(X38)|~v1_funct_2(X38,X35,X36)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&(X37!=X38|r1_funct_2(X33,X34,X35,X36,X37,X38)|(v1_xboole_0(X34)|v1_xboole_0(X36)|~v1_funct_1(X37)|~v1_funct_2(X37,X33,X34)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|~v1_funct_1(X38)|~v1_funct_2(X38,X35,X36)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.18/0.51  cnf(c_0_48, negated_conjecture, (r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  cnf(c_0_49, negated_conjecture, (~r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk10_0),esk9_0)|~r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  cnf(c_0_50, negated_conjecture, (k3_tmap_1(X1,esk5_0,esk4_0,esk6_0,esk10_0)=k2_tmap_1(esk4_0,esk5_0,esk10_0,esk6_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_34]), c_0_39])).
% 0.18/0.51  cnf(c_0_51, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_40, c_0_17])).
% 0.18/0.51  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  fof(c_0_53, plain, ![X18, X19, X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X21,X20)|(r2_hidden(X21,X18)|r2_hidden(X21,X19))|X20!=k2_xboole_0(X18,X19))&((~r2_hidden(X22,X18)|r2_hidden(X22,X20)|X20!=k2_xboole_0(X18,X19))&(~r2_hidden(X22,X19)|r2_hidden(X22,X20)|X20!=k2_xboole_0(X18,X19))))&(((~r2_hidden(esk3_3(X23,X24,X25),X23)|~r2_hidden(esk3_3(X23,X24,X25),X25)|X25=k2_xboole_0(X23,X24))&(~r2_hidden(esk3_3(X23,X24,X25),X24)|~r2_hidden(esk3_3(X23,X24,X25),X25)|X25=k2_xboole_0(X23,X24)))&(r2_hidden(esk3_3(X23,X24,X25),X25)|(r2_hidden(esk3_3(X23,X24,X25),X23)|r2_hidden(esk3_3(X23,X24,X25),X24))|X25=k2_xboole_0(X23,X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.18/0.51  cnf(c_0_54, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.51  cnf(c_0_55, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.51  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0)))|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.18/0.51  cnf(c_0_57, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.51  cnf(c_0_58, negated_conjecture, (r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk10_0),esk9_0)|r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  cnf(c_0_59, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.18/0.51  cnf(c_0_60, negated_conjecture, (r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk8_0,esk10_0)), inference(rw,[status(thm)],[c_0_48, c_0_17])).
% 0.18/0.51  cnf(c_0_61, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  cnf(c_0_62, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.51  cnf(c_0_63, negated_conjecture, (~r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k3_tmap_1(esk4_0,esk5_0,esk4_0,esk6_0,esk10_0),esk9_0)|~r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0)), inference(rw,[status(thm)],[c_0_49, c_0_17])).
% 0.18/0.51  cnf(c_0_64, negated_conjecture, (k3_tmap_1(esk4_0,esk5_0,esk4_0,esk6_0,esk10_0)=k2_tmap_1(esk4_0,esk5_0,esk10_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_24]), c_0_26])]), c_0_30])).
% 0.18/0.51  cnf(c_0_65, negated_conjecture, (r1_tarski(esk10_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_36, c_0_28])).
% 0.18/0.51  cnf(c_0_66, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_36, c_0_52])).
% 0.18/0.51  cnf(c_0_67, plain, (r2_hidden(esk3_3(X1,X2,X3),X3)|r2_hidden(esk3_3(X1,X2,X3),X1)|r2_hidden(esk3_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.18/0.51  cnf(c_0_68, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.18/0.51  cnf(c_0_69, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.51  cnf(c_0_70, negated_conjecture, (r2_hidden(esk1_1(esk9_0),k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0)))|v1_xboole_0(esk9_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.18/0.51  fof(c_0_71, plain, ![X29, X30]:(~v1_xboole_0(X30)|v1_xboole_0(k2_zfmisc_1(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).
% 0.18/0.51  cnf(c_0_72, negated_conjecture, (r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k3_tmap_1(esk4_0,esk5_0,esk4_0,esk6_0,esk10_0),esk9_0)|r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0)), inference(rw,[status(thm)],[c_0_58, c_0_17])).
% 0.18/0.51  cnf(c_0_73, negated_conjecture, (esk10_0=esk8_0|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_22]), c_0_61]), c_0_27]), c_0_62]), c_0_28]), c_0_52])])).
% 0.18/0.51  cnf(c_0_74, negated_conjecture, (~r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk10_0,esk6_0),esk9_0)|~r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0)), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 0.18/0.51  cnf(c_0_75, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_44, c_0_65])).
% 0.18/0.51  cnf(c_0_76, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_44, c_0_66])).
% 0.18/0.51  cnf(c_0_77, plain, (X1=X2|r2_hidden(esk3_3(X2,X2,X1),X2)|r2_hidden(esk3_3(X2,X2,X1),X1)), inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_67]), c_0_68])).
% 0.18/0.51  cnf(c_0_78, negated_conjecture, (v1_xboole_0(esk9_0)|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.18/0.51  cnf(c_0_79, plain, (v1_xboole_0(k2_zfmisc_1(X2,X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.18/0.51  cnf(c_0_80, negated_conjecture, (r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k3_tmap_1(esk4_0,esk5_0,esk4_0,esk6_0,esk8_0),esk9_0)|r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.18/0.51  cnf(c_0_81, negated_conjecture, (k3_tmap_1(esk4_0,esk5_0,esk4_0,esk6_0,esk8_0)=k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_64, c_0_73])).
% 0.18/0.51  cnf(c_0_82, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|~r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0)), inference(spm,[status(thm)],[c_0_74, c_0_73])).
% 0.18/0.51  cnf(c_0_83, negated_conjecture, (r2_hidden(esk1_1(esk10_0),k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))|v1_xboole_0(esk10_0)), inference(spm,[status(thm)],[c_0_75, c_0_57])).
% 0.18/0.51  cnf(c_0_84, negated_conjecture, (r2_hidden(esk1_1(esk8_0),k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))|v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_76, c_0_57])).
% 0.18/0.51  cnf(c_0_85, plain, (X1=X2|r2_hidden(esk3_3(X2,X2,X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_69, c_0_77])).
% 0.18/0.51  cnf(c_0_86, negated_conjecture, (v1_xboole_0(esk9_0)|~v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.18/0.51  cnf(c_0_87, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])).
% 0.18/0.51  cnf(c_0_88, negated_conjecture, (v1_xboole_0(esk10_0)|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_69, c_0_83])).
% 0.18/0.51  cnf(c_0_89, negated_conjecture, (v1_xboole_0(esk8_0)|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_69, c_0_84])).
% 0.18/0.51  cnf(c_0_90, plain, (X1=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_69, c_0_85])).
% 0.18/0.51  cnf(c_0_91, negated_conjecture, (v1_xboole_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87])])).
% 0.18/0.51  cnf(c_0_92, negated_conjecture, (v1_xboole_0(esk10_0)|~v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_88, c_0_79])).
% 0.18/0.51  cnf(c_0_93, negated_conjecture, (v1_xboole_0(esk8_0)|~v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_89, c_0_79])).
% 0.18/0.51  cnf(c_0_94, negated_conjecture, (esk9_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.18/0.51  cnf(c_0_95, negated_conjecture, (v1_xboole_0(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_87])])).
% 0.18/0.51  cnf(c_0_96, negated_conjecture, (v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_87])])).
% 0.18/0.51  cnf(c_0_97, negated_conjecture, (esk10_0=esk9_0), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.18/0.51  cnf(c_0_98, negated_conjecture, (esk8_0=esk9_0), inference(spm,[status(thm)],[c_0_94, c_0_96])).
% 0.18/0.51  cnf(c_0_99, negated_conjecture, (u1_struct_0(esk5_0)=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_90, c_0_87])).
% 0.18/0.51  cnf(c_0_100, negated_conjecture, (~r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk9_0,esk6_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_97]), c_0_98])])).
% 0.18/0.51  cnf(c_0_101, negated_conjecture, (esk9_0=u1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_99, c_0_91])).
% 0.18/0.51  cnf(c_0_102, negated_conjecture, (r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk8_0,esk6_0),esk9_0)|r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,esk10_0,esk6_0),esk9_0)), inference(rw,[status(thm)],[c_0_72, c_0_64])).
% 0.18/0.51  cnf(c_0_103, negated_conjecture, (~r2_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),k2_tmap_1(esk4_0,esk5_0,u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_101]), c_0_101])).
% 0.18/0.51  cnf(c_0_104, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_97]), c_0_98]), c_0_101]), c_0_101]), c_0_101]), c_0_101])]), c_0_103]), ['proof']).
% 0.18/0.51  # SZS output end CNFRefutation
% 0.18/0.51  # Proof object total steps             : 105
% 0.18/0.51  # Proof object clause steps            : 82
% 0.18/0.51  # Proof object formula steps           : 23
% 0.18/0.51  # Proof object conjectures             : 66
% 0.18/0.51  # Proof object clause conjectures      : 63
% 0.18/0.51  # Proof object formula conjectures     : 3
% 0.18/0.51  # Proof object initial clauses used    : 32
% 0.18/0.51  # Proof object initial formulas used   : 11
% 0.18/0.51  # Proof object generating inferences   : 35
% 0.18/0.51  # Proof object simplifying inferences  : 57
% 0.18/0.51  # Training examples: 0 positive, 0 negative
% 0.18/0.51  # Parsed axioms                        : 11
% 0.18/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.51  # Initial clauses                      : 43
% 0.18/0.51  # Removed in clause preprocessing      : 0
% 0.18/0.51  # Initial clauses in saturation        : 43
% 0.18/0.51  # Processed clauses                    : 1498
% 0.18/0.51  # ...of these trivial                  : 20
% 0.18/0.51  # ...subsumed                          : 983
% 0.18/0.51  # ...remaining for further processing  : 494
% 0.18/0.51  # Other redundant clauses eliminated   : 4
% 0.18/0.51  # Clauses deleted for lack of memory   : 0
% 0.18/0.51  # Backward-subsumed                    : 10
% 0.18/0.51  # Backward-rewritten                   : 260
% 0.18/0.51  # Generated clauses                    : 8404
% 0.18/0.51  # ...of the previous two non-trivial   : 7802
% 0.18/0.51  # Contextual simplify-reflections      : 4
% 0.18/0.51  # Paramodulations                      : 8178
% 0.18/0.51  # Factorizations                       : 222
% 0.18/0.51  # Equation resolutions                 : 4
% 0.18/0.51  # Propositional unsat checks           : 0
% 0.18/0.51  #    Propositional check models        : 0
% 0.18/0.51  #    Propositional check unsatisfiable : 0
% 0.18/0.51  #    Propositional clauses             : 0
% 0.18/0.51  #    Propositional clauses after purity: 0
% 0.18/0.51  #    Propositional unsat core size     : 0
% 0.18/0.51  #    Propositional preprocessing time  : 0.000
% 0.18/0.51  #    Propositional encoding time       : 0.000
% 0.18/0.51  #    Propositional solver time         : 0.000
% 0.18/0.51  #    Success case prop preproc time    : 0.000
% 0.18/0.51  #    Success case prop encoding time   : 0.000
% 0.18/0.51  #    Success case prop solver time     : 0.000
% 0.18/0.51  # Current number of processed clauses  : 178
% 0.18/0.51  #    Positive orientable unit clauses  : 36
% 0.18/0.51  #    Positive unorientable unit clauses: 0
% 0.18/0.51  #    Negative unit clauses             : 4
% 0.18/0.51  #    Non-unit-clauses                  : 138
% 0.18/0.51  # Current number of unprocessed clauses: 6332
% 0.18/0.51  # ...number of literals in the above   : 26810
% 0.18/0.51  # Current number of archived formulas  : 0
% 0.18/0.51  # Current number of archived clauses   : 312
% 0.18/0.51  # Clause-clause subsumption calls (NU) : 47779
% 0.18/0.51  # Rec. Clause-clause subsumption calls : 26371
% 0.18/0.51  # Non-unit clause-clause subsumptions  : 996
% 0.18/0.51  # Unit Clause-clause subsumption calls : 3263
% 0.18/0.51  # Rewrite failures with RHS unbound    : 0
% 0.18/0.51  # BW rewrite match attempts            : 140
% 0.18/0.51  # BW rewrite match successes           : 65
% 0.18/0.51  # Condensation attempts                : 0
% 0.18/0.51  # Condensation successes               : 0
% 0.18/0.51  # Termbank termtop insertions          : 125277
% 0.18/0.51  
% 0.18/0.51  # -------------------------------------------------
% 0.18/0.51  # User time                : 0.168 s
% 0.18/0.51  # System time              : 0.011 s
% 0.18/0.51  # Total time               : 0.179 s
% 0.18/0.51  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
