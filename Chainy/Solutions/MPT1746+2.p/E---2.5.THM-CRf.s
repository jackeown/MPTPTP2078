%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1746+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:07 EST 2020

% Result     : Theorem 36.76s
% Output     : CNFRefutation 36.76s
% Verified   : 
% Statistics : Number of formulae       :   29 ( 331 expanded)
%              Number of clauses        :   24 (  95 expanded)
%              Number of leaves         :    2 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  177 (5027 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_tmap_1,conjecture,(
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
             => ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & v5_pre_topc(X3,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => r1_tmap_1(X1,X2,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tmap_1)).

fof(t49_tmap_1,axiom,(
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
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ( v5_pre_topc(X3,X2,X1)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => r1_tmap_1(X2,X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
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
               => ( ( v1_funct_1(X3)
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                    & v5_pre_topc(X3,X1,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                <=> ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => r1_tmap_1(X1,X2,X3,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t55_tmap_1])).

fof(c_0_3,plain,(
    ! [X10884,X10885,X10886,X10887] :
      ( ( ~ v5_pre_topc(X10886,X10885,X10884)
        | ~ m1_subset_1(X10887,u1_struct_0(X10885))
        | r1_tmap_1(X10885,X10884,X10886,X10887)
        | ~ v1_funct_1(X10886)
        | ~ v1_funct_2(X10886,u1_struct_0(X10885),u1_struct_0(X10884))
        | ~ m1_subset_1(X10886,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10885),u1_struct_0(X10884))))
        | v2_struct_0(X10885)
        | ~ v2_pre_topc(X10885)
        | ~ l1_pre_topc(X10885)
        | v2_struct_0(X10884)
        | ~ v2_pre_topc(X10884)
        | ~ l1_pre_topc(X10884) )
      & ( m1_subset_1(esk1275_3(X10884,X10885,X10886),u1_struct_0(X10885))
        | v5_pre_topc(X10886,X10885,X10884)
        | ~ v1_funct_1(X10886)
        | ~ v1_funct_2(X10886,u1_struct_0(X10885),u1_struct_0(X10884))
        | ~ m1_subset_1(X10886,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10885),u1_struct_0(X10884))))
        | v2_struct_0(X10885)
        | ~ v2_pre_topc(X10885)
        | ~ l1_pre_topc(X10885)
        | v2_struct_0(X10884)
        | ~ v2_pre_topc(X10884)
        | ~ l1_pre_topc(X10884) )
      & ( ~ r1_tmap_1(X10885,X10884,X10886,esk1275_3(X10884,X10885,X10886))
        | v5_pre_topc(X10886,X10885,X10884)
        | ~ v1_funct_1(X10886)
        | ~ v1_funct_2(X10886,u1_struct_0(X10885),u1_struct_0(X10884))
        | ~ m1_subset_1(X10886,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10885),u1_struct_0(X10884))))
        | v2_struct_0(X10885)
        | ~ v2_pre_topc(X10885)
        | ~ l1_pre_topc(X10885)
        | v2_struct_0(X10884)
        | ~ v2_pre_topc(X10884)
        | ~ l1_pre_topc(X10884) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

fof(c_0_4,negated_conjecture,(
    ! [X10929] :
      ( ~ v2_struct_0(esk1276_0)
      & v2_pre_topc(esk1276_0)
      & l1_pre_topc(esk1276_0)
      & ~ v2_struct_0(esk1277_0)
      & v2_pre_topc(esk1277_0)
      & l1_pre_topc(esk1277_0)
      & v1_funct_1(esk1278_0)
      & v1_funct_2(esk1278_0,u1_struct_0(esk1276_0),u1_struct_0(esk1277_0))
      & m1_subset_1(esk1278_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1276_0),u1_struct_0(esk1277_0))))
      & ( m1_subset_1(esk1279_0,u1_struct_0(esk1276_0))
        | ~ v1_funct_1(esk1278_0)
        | ~ v1_funct_2(esk1278_0,u1_struct_0(esk1276_0),u1_struct_0(esk1277_0))
        | ~ v5_pre_topc(esk1278_0,esk1276_0,esk1277_0)
        | ~ m1_subset_1(esk1278_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1276_0),u1_struct_0(esk1277_0)))) )
      & ( ~ r1_tmap_1(esk1276_0,esk1277_0,esk1278_0,esk1279_0)
        | ~ v1_funct_1(esk1278_0)
        | ~ v1_funct_2(esk1278_0,u1_struct_0(esk1276_0),u1_struct_0(esk1277_0))
        | ~ v5_pre_topc(esk1278_0,esk1276_0,esk1277_0)
        | ~ m1_subset_1(esk1278_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1276_0),u1_struct_0(esk1277_0)))) )
      & ( v1_funct_1(esk1278_0)
        | ~ m1_subset_1(X10929,u1_struct_0(esk1276_0))
        | r1_tmap_1(esk1276_0,esk1277_0,esk1278_0,X10929) )
      & ( v1_funct_2(esk1278_0,u1_struct_0(esk1276_0),u1_struct_0(esk1277_0))
        | ~ m1_subset_1(X10929,u1_struct_0(esk1276_0))
        | r1_tmap_1(esk1276_0,esk1277_0,esk1278_0,X10929) )
      & ( v5_pre_topc(esk1278_0,esk1276_0,esk1277_0)
        | ~ m1_subset_1(X10929,u1_struct_0(esk1276_0))
        | r1_tmap_1(esk1276_0,esk1277_0,esk1278_0,X10929) )
      & ( m1_subset_1(esk1278_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1276_0),u1_struct_0(esk1277_0))))
        | ~ m1_subset_1(X10929,u1_struct_0(esk1276_0))
        | r1_tmap_1(esk1276_0,esk1277_0,esk1278_0,X10929) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])])).

cnf(c_0_5,plain,
    ( r1_tmap_1(X2,X3,X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( v1_funct_2(esk1278_0,u1_struct_0(esk1276_0),u1_struct_0(esk1277_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v2_pre_topc(esk1277_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v2_pre_topc(esk1276_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( l1_pre_topc(esk1277_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk1276_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_1(esk1278_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk1278_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1276_0),u1_struct_0(esk1277_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1277_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1276_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( v5_pre_topc(esk1278_0,esk1276_0,esk1277_0)
    | r1_tmap_1(esk1276_0,esk1277_0,esk1278_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1276_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk1275_3(X1,X2,X3),u1_struct_0(X2))
    | v5_pre_topc(X3,X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_17,negated_conjecture,
    ( r1_tmap_1(esk1276_0,esk1277_0,esk1278_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1276_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])]),c_0_13]),c_0_14]),c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( v5_pre_topc(esk1278_0,esk1276_0,esk1277_0)
    | m1_subset_1(esk1275_3(esk1277_0,esk1276_0,esk1278_0),u1_struct_0(esk1276_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_6]),c_0_8]),c_0_7]),c_0_10]),c_0_9]),c_0_11]),c_0_12])]),c_0_14]),c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk1279_0,u1_struct_0(esk1276_0))
    | ~ v1_funct_1(esk1278_0)
    | ~ v1_funct_2(esk1278_0,u1_struct_0(esk1276_0),u1_struct_0(esk1277_0))
    | ~ v5_pre_topc(esk1278_0,esk1276_0,esk1277_0)
    | ~ m1_subset_1(esk1278_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1276_0),u1_struct_0(esk1277_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,plain,
    ( v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,X3,esk1275_3(X2,X1,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_21,negated_conjecture,
    ( r1_tmap_1(esk1276_0,esk1277_0,esk1278_0,esk1275_3(esk1277_0,esk1276_0,esk1278_0))
    | v5_pre_topc(esk1278_0,esk1276_0,esk1277_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tmap_1(esk1276_0,esk1277_0,esk1278_0,esk1279_0)
    | ~ v1_funct_1(esk1278_0)
    | ~ v1_funct_2(esk1278_0,u1_struct_0(esk1276_0),u1_struct_0(esk1277_0))
    | ~ v5_pre_topc(esk1278_0,esk1276_0,esk1277_0)
    | ~ m1_subset_1(esk1278_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1276_0),u1_struct_0(esk1277_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk1279_0,u1_struct_0(esk1276_0))
    | ~ v5_pre_topc(esk1278_0,esk1276_0,esk1277_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_11]),c_0_6]),c_0_12])])).

cnf(c_0_24,negated_conjecture,
    ( v5_pre_topc(esk1278_0,esk1276_0,esk1277_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_6]),c_0_11]),c_0_12])]),c_0_13]),c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_tmap_1(esk1276_0,esk1277_0,esk1278_0,esk1279_0)
    | ~ v5_pre_topc(esk1278_0,esk1276_0,esk1277_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_11]),c_0_6]),c_0_12])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk1279_0,u1_struct_0(esk1276_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_tmap_1(esk1276_0,esk1277_0,esk1278_0,esk1279_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_26]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
