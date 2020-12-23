%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1781+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:44 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 459 expanded)
%              Number of clauses        :   47 ( 151 expanded)
%              Number of leaves         :   11 ( 116 expanded)
%              Depth                    :   15
%              Number of atoms          :  328 (3724 expanded)
%              Number of equality atoms :   33 ( 282 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   48 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

fof(d7_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => k4_tmap_1(X1,X2) = k2_tmap_1(X1,X1,k3_struct_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

fof(dt_k3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ( v1_funct_1(k3_struct_0(X1))
        & v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))
        & m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(t35_funct_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k1_funct_1(k6_relat_1(X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(d4_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k3_struct_0(X1) = k6_partfun1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_struct_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | k4_tmap_1(X8,X9) = k2_tmap_1(X8,X8,k3_struct_0(X8),X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_tmap_1])])])])).

fof(c_0_13,negated_conjecture,(
    ! [X31] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk2_0)
      & v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
      & ( ~ m1_subset_1(X31,u1_struct_0(esk2_0))
        | ~ r2_hidden(X31,u1_struct_0(esk3_0))
        | X31 = k1_funct_1(esk4_0,X31) )
      & ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

fof(c_0_14,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( ( m1_subset_1(esk1_5(X22,X23,X24,X25,X26),u1_struct_0(X23))
        | r2_funct_2(u1_struct_0(X24),u1_struct_0(X22),k2_tmap_1(X23,X22,X25,X24),X26)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X22))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X22))))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22))))
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( r2_hidden(esk1_5(X22,X23,X24,X25,X26),u1_struct_0(X24))
        | r2_funct_2(u1_struct_0(X24),u1_struct_0(X22),k2_tmap_1(X23,X22,X25,X24),X26)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X22))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X22))))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22))))
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( k3_funct_2(u1_struct_0(X23),u1_struct_0(X22),X25,esk1_5(X22,X23,X24,X25,X26)) != k1_funct_1(X26,esk1_5(X22,X23,X24,X25,X26))
        | r2_funct_2(u1_struct_0(X24),u1_struct_0(X22),k2_tmap_1(X23,X22,X25,X24),X26)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X22))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X22))))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22))))
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | k4_tmap_1(X1,X2) = k2_tmap_1(X1,X1,k3_struct_0(X1),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_5(X1,X2,X3,X4,X5),u1_struct_0(X3))
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k2_tmap_1(esk2_0,esk2_0,k3_struct_0(esk2_0),esk3_0) = k4_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,plain,(
    ! [X10] :
      ( ( v1_funct_1(k3_struct_0(X10))
        | ~ l1_struct_0(X10) )
      & ( v1_funct_2(k3_struct_0(X10),u1_struct_0(X10),u1_struct_0(X10))
        | ~ l1_struct_0(X10) )
      & ( m1_subset_1(k3_struct_0(X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X10))))
        | ~ l1_struct_0(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_struct_0])])])).

cnf(c_0_24,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),X1)
    | r2_hidden(esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),X1),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k3_struct_0(esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k3_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_struct_0(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_16]),c_0_17]),c_0_18])]),c_0_22]),c_0_19])).

cnf(c_0_25,plain,
    ( v1_funct_1(k3_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(X11)
      | l1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,X4,X5),u1_struct_0(X2))
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),X1)
    | r2_hidden(esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),X1),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_31,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),X1)
    | m1_subset_1(esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k3_struct_0(esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k3_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_struct_0(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_21]),c_0_16]),c_0_17]),c_0_18])]),c_0_22]),c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),X1)
    | r2_hidden(esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),X1),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_17])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),X1)
    | m1_subset_1(esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_25]),c_0_26]),c_0_27])).

fof(c_0_39,plain,(
    ! [X13,X14,X15,X16] :
      ( v1_xboole_0(X13)
      | ~ v1_funct_1(X15)
      | ~ v1_funct_2(X15,X13,X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | ~ m1_subset_1(X16,X13)
      | k3_funct_2(X13,X14,X15,X16) = k1_funct_1(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_40,negated_conjecture,
    ( X1 = k1_funct_1(esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),X1)
    | m1_subset_1(esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_31]),c_0_17])])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X3,X4),X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_5(X2,X1,X4,X3,X5)) != k1_funct_1(X5,esk1_5(X2,X1,X4,X3,X5))
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0)) = esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0)
    | ~ m1_subset_1(esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_47,plain,
    ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),X2) = k1_funct_1(k3_struct_0(X1),X2)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_27]),c_0_25]),c_0_26])).

fof(c_0_48,plain,(
    ! [X20,X21] :
      ( ~ r2_hidden(X20,X21)
      | k1_funct_1(k6_relat_1(X21),X20) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_1])])).

fof(c_0_49,plain,(
    ! [X17] : k6_partfun1(X17) = k6_relat_1(X17) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_50,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk3_0),esk4_0)
    | v2_struct_0(X1)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),X2,esk1_5(esk2_0,X1,esk3_0,X2,esk4_0)) != k1_funct_1(esk4_0,esk1_5(esk2_0,X1,esk3_0,X2,esk4_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_34]),c_0_35]),c_0_36]),c_0_17]),c_0_18])]),c_0_22]),c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0)) = esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_52,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k3_struct_0(esk2_0),esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0)) = k1_funct_1(k3_struct_0(esk2_0),esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_53,plain,
    ( k1_funct_1(k6_relat_1(X2),X1) = X1
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_55,plain,(
    ! [X7] :
      ( ~ l1_struct_0(X7)
      | k3_struct_0(X7) = k6_partfun1(u1_struct_0(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_struct_0])])).

fof(c_0_56,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X18,X19)
      | v1_xboole_0(X19)
      | r2_hidden(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_57,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k3_struct_0(esk2_0),esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0)) != esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_27]),c_0_21]),c_0_51]),c_0_16]),c_0_17]),c_0_18])]),c_0_37]),c_0_19]),c_0_25]),c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k3_struct_0(esk2_0),esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0)) = k1_funct_1(k3_struct_0(esk2_0),esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_31]),c_0_17])])).

cnf(c_0_59,plain,
    ( k1_funct_1(k6_partfun1(X2),X1) = X1
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,plain,
    ( k3_struct_0(X1) = k6_partfun1(u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_62,plain,(
    ! [X12] :
      ( v2_struct_0(X12)
      | ~ l1_struct_0(X12)
      | ~ v1_xboole_0(u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | k1_funct_1(k3_struct_0(esk2_0),esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0)) != esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,plain,
    ( k1_funct_1(k3_struct_0(X1),X2) = X2
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_5(esk2_0,esk2_0,esk3_0,k3_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_46])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_19])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_31]),c_0_17])]),
    [proof]).

%------------------------------------------------------------------------------
