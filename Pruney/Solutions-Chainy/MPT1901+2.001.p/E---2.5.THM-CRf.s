%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:01 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 255 expanded)
%              Number of clauses        :   25 (  81 expanded)
%              Number of leaves         :    6 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  235 (2064 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   33 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t69_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => v5_pre_topc(X3,X1,X2) ) )
       => v1_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tex_2)).

fof(t17_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(t113_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> ( v1_funct_1(k7_tmap_1(X1,X2))
              & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
              & v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
              & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).

fof(fc4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_struct_0(k6_tmap_1(X1,X2))
        & v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ( ! [X2] :
              ( ( ~ v2_struct_0(X2)
                & v2_pre_topc(X2)
                & l1_pre_topc(X2) )
             => ! [X3] :
                  ( ( v1_funct_1(X3)
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                 => v5_pre_topc(X3,X1,X2) ) )
         => v1_tdlat_3(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t69_tex_2])).

fof(c_0_7,plain,(
    ! [X12,X13] :
      ( ( ~ v1_tdlat_3(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v3_pre_topc(X13,X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk1_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | v1_tdlat_3(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ v3_pre_topc(esk1_1(X12),X12)
        | v1_tdlat_3(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X16,X17] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ( v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(esk2_0),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X16))))
        | v5_pre_topc(X17,esk2_0,X16) )
      & ~ v1_tdlat_3(esk2_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])).

fof(c_0_9,plain,(
    ! [X6,X7] :
      ( ( v1_funct_1(k7_tmap_1(X6,X7))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) )
      & ( v1_funct_2(k7_tmap_1(X6,X7),u1_struct_0(X6),u1_struct_0(k6_tmap_1(X6,X7)))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) )
      & ( m1_subset_1(k7_tmap_1(X6,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(k6_tmap_1(X6,X7)))))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( ~ v1_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X4,X5] :
      ( ( v1_pre_topc(k6_tmap_1(X4,X5))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) )
      & ( v2_pre_topc(k6_tmap_1(X4,X5))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) )
      & ( l1_pre_topc(k6_tmap_1(X4,X5))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

fof(c_0_15,plain,(
    ! [X10,X11] :
      ( ( v1_funct_1(k7_tmap_1(X10,X11))
        | ~ v3_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v1_funct_2(k7_tmap_1(X10,X11),u1_struct_0(X10),u1_struct_0(k6_tmap_1(X10,X11)))
        | ~ v3_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v5_pre_topc(k7_tmap_1(X10,X11),X10,k6_tmap_1(X10,X11))
        | ~ v3_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(k7_tmap_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(k6_tmap_1(X10,X11)))))
        | ~ v3_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ v1_funct_1(k7_tmap_1(X10,X11))
        | ~ v1_funct_2(k7_tmap_1(X10,X11),u1_struct_0(X10),u1_struct_0(k6_tmap_1(X10,X11)))
        | ~ v5_pre_topc(k7_tmap_1(X10,X11),X10,k6_tmap_1(X10,X11))
        | ~ m1_subset_1(k7_tmap_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(k6_tmap_1(X10,X11)))))
        | v3_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk1_1(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( v3_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k7_tmap_1(X1,X2))
    | ~ v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | ~ v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | ~ m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v2_struct_0(X1)
    | v5_pre_topc(X2,esk2_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk2_0,esk1_1(esk2_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk1_1(esk2_0)))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_11]),c_0_12])]),c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk2_0,esk1_1(esk2_0)),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk1_1(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_17]),c_0_11]),c_0_12])]),c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk2_0,esk1_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_11]),c_0_12])]),c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk2_0,esk1_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_11]),c_0_12])]),c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk2_0,esk1_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_11]),c_0_12])]),c_0_18])).

fof(c_0_30,plain,(
    ! [X8,X9] :
      ( ( ~ v2_struct_0(k6_tmap_1(X8,X9))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))) )
      & ( v1_pre_topc(k6_tmap_1(X8,X9))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))) )
      & ( v2_pre_topc(k6_tmap_1(X8,X9))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).

cnf(c_0_31,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_23,c_0_16]),c_0_20]),c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk1_1(esk2_0)),esk2_0,k6_tmap_1(esk2_0,esk1_1(esk2_0)))
    | v2_struct_0(k6_tmap_1(esk2_0,esk1_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( v3_pre_topc(esk1_1(esk2_0),esk2_0)
    | v2_struct_0(k6_tmap_1(esk2_0,esk1_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_17]),c_0_11]),c_0_12])]),c_0_18])).

cnf(c_0_35,plain,
    ( v1_tdlat_3(X1)
    | ~ v3_pre_topc(esk1_1(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,negated_conjecture,
    ( v3_pre_topc(esk1_1(esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_17]),c_0_11]),c_0_12])]),c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_11]),c_0_12])]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:05:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t69_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>v5_pre_topc(X3,X1,X2)))=>v1_tdlat_3(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tex_2)).
% 0.12/0.37  fof(t17_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 0.12/0.37  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.12/0.37  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 0.12/0.37  fof(t113_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_tmap_1)).
% 0.12/0.37  fof(fc4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((~(v2_struct_0(k6_tmap_1(X1,X2)))&v1_pre_topc(k6_tmap_1(X1,X2)))&v2_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tmap_1)).
% 0.12/0.37  fof(c_0_6, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>v5_pre_topc(X3,X1,X2)))=>v1_tdlat_3(X1)))), inference(assume_negation,[status(cth)],[t69_tex_2])).
% 0.12/0.37  fof(c_0_7, plain, ![X12, X13]:((~v1_tdlat_3(X12)|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|v3_pre_topc(X13,X12))|(~v2_pre_topc(X12)|~l1_pre_topc(X12)))&((m1_subset_1(esk1_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|v1_tdlat_3(X12)|(~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~v3_pre_topc(esk1_1(X12),X12)|v1_tdlat_3(X12)|(~v2_pre_topc(X12)|~l1_pre_topc(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).
% 0.12/0.37  fof(c_0_8, negated_conjecture, ![X16, X17]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(esk2_0),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X16))))|v5_pre_topc(X17,esk2_0,X16)))&~v1_tdlat_3(esk2_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])).
% 0.12/0.37  fof(c_0_9, plain, ![X6, X7]:(((v1_funct_1(k7_tmap_1(X6,X7))|(v2_struct_0(X6)|~v2_pre_topc(X6)|~l1_pre_topc(X6)|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))))&(v1_funct_2(k7_tmap_1(X6,X7),u1_struct_0(X6),u1_struct_0(k6_tmap_1(X6,X7)))|(v2_struct_0(X6)|~v2_pre_topc(X6)|~l1_pre_topc(X6)|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))))))&(m1_subset_1(k7_tmap_1(X6,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(k6_tmap_1(X6,X7)))))|(v2_struct_0(X6)|~v2_pre_topc(X6)|~l1_pre_topc(X6)|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.12/0.37  cnf(c_0_10, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v1_tdlat_3(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_11, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (~v1_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_14, plain, ![X4, X5]:(((v1_pre_topc(k6_tmap_1(X4,X5))|(v2_struct_0(X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))))&(v2_pre_topc(k6_tmap_1(X4,X5))|(v2_struct_0(X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))))))&(l1_pre_topc(k6_tmap_1(X4,X5))|(v2_struct_0(X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 0.12/0.37  fof(c_0_15, plain, ![X10, X11]:(((((v1_funct_1(k7_tmap_1(X10,X11))|~v3_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(v1_funct_2(k7_tmap_1(X10,X11),u1_struct_0(X10),u1_struct_0(k6_tmap_1(X10,X11)))|~v3_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(v5_pre_topc(k7_tmap_1(X10,X11),X10,k6_tmap_1(X10,X11))|~v3_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(m1_subset_1(k7_tmap_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(k6_tmap_1(X10,X11)))))|~v3_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(~v1_funct_1(k7_tmap_1(X10,X11))|~v1_funct_2(k7_tmap_1(X10,X11),u1_struct_0(X10),u1_struct_0(k6_tmap_1(X10,X11)))|~v5_pre_topc(k7_tmap_1(X10,X11),X10,k6_tmap_1(X10,X11))|~m1_subset_1(k7_tmap_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(k6_tmap_1(X10,X11)))))|v3_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).
% 0.12/0.37  cnf(c_0_16, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk1_1(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])]), c_0_13])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_19, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_20, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_21, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_22, plain, (v2_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_23, plain, (v3_pre_topc(X2,X1)|v2_struct_0(X1)|~v1_funct_1(k7_tmap_1(X1,X2))|~v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|~v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|~m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (v2_struct_0(X1)|v5_pre_topc(X2,esk2_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_1(X2)|~v1_funct_2(X2,u1_struct_0(esk2_0),u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X1))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (m1_subset_1(k7_tmap_1(esk2_0,esk1_1(esk2_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk1_1(esk2_0))))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_11]), c_0_12])]), c_0_18])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (v1_funct_2(k7_tmap_1(esk2_0,esk1_1(esk2_0)),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk1_1(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_17]), c_0_11]), c_0_12])]), c_0_18])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (v1_funct_1(k7_tmap_1(esk2_0,esk1_1(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_17]), c_0_11]), c_0_12])]), c_0_18])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk2_0,esk1_1(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_11]), c_0_12])]), c_0_18])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (v2_pre_topc(k6_tmap_1(esk2_0,esk1_1(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_17]), c_0_11]), c_0_12])]), c_0_18])).
% 0.12/0.37  fof(c_0_30, plain, ![X8, X9]:(((~v2_struct_0(k6_tmap_1(X8,X9))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))))&(v1_pre_topc(k6_tmap_1(X8,X9))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))))))&(v2_pre_topc(k6_tmap_1(X8,X9))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).
% 0.12/0.37  cnf(c_0_31, plain, (v3_pre_topc(X1,X2)|v2_struct_0(X2)|~v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_23, c_0_16]), c_0_20]), c_0_19])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk1_1(esk2_0)),esk2_0,k6_tmap_1(esk2_0,esk1_1(esk2_0)))|v2_struct_0(k6_tmap_1(esk2_0,esk1_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])])).
% 0.12/0.37  cnf(c_0_33, plain, (v2_struct_0(X1)|~v2_struct_0(k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (v3_pre_topc(esk1_1(esk2_0),esk2_0)|v2_struct_0(k6_tmap_1(esk2_0,esk1_1(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_17]), c_0_11]), c_0_12])]), c_0_18])).
% 0.12/0.37  cnf(c_0_35, plain, (v1_tdlat_3(X1)|~v3_pre_topc(esk1_1(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (v3_pre_topc(esk1_1(esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_17]), c_0_11]), c_0_12])]), c_0_18])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_11]), c_0_12])]), c_0_13]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 38
% 0.12/0.37  # Proof object clause steps            : 25
% 0.12/0.37  # Proof object formula steps           : 13
% 0.12/0.37  # Proof object conjectures             : 18
% 0.12/0.37  # Proof object clause conjectures      : 15
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 14
% 0.12/0.37  # Proof object initial formulas used   : 6
% 0.12/0.37  # Proof object generating inferences   : 10
% 0.12/0.37  # Proof object simplifying inferences  : 45
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 6
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 22
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 22
% 0.12/0.37  # Processed clauses                    : 54
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 5
% 0.12/0.37  # ...remaining for further processing  : 49
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 2
% 0.12/0.37  # Generated clauses                    : 23
% 0.12/0.37  # ...of the previous two non-trivial   : 21
% 0.12/0.37  # Contextual simplify-reflections      : 3
% 0.12/0.37  # Paramodulations                      : 23
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 30
% 0.12/0.37  #    Positive orientable unit clauses  : 10
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 2
% 0.12/0.37  #    Non-unit-clauses                  : 18
% 0.12/0.37  # Current number of unprocessed clauses: 5
% 0.12/0.37  # ...number of literals in the above   : 18
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 19
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 195
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 9
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 8
% 0.12/0.37  # Unit Clause-clause subsumption calls : 30
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 1
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3341
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.027 s
% 0.12/0.37  # System time              : 0.007 s
% 0.12/0.37  # Total time               : 0.034 s
% 0.12/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
