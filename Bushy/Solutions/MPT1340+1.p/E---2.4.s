%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t64_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:42 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 176 expanded)
%              Number of clauses        :   31 (  56 expanded)
%              Number of leaves         :    9 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  232 (1152 expanded)
%              Number of equality atoms :   49 ( 153 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_tops_2,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t64_tops_2.p',t64_tops_2)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t64_tops_2.p',d4_tops_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t64_tops_2.p',cc1_relset_1)).

fof(dt_k2_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_tops_2(X1,X2,X3))
        & v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
        & m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t64_tops_2.p',dt_k2_tops_2)).

fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t64_tops_2.p',t65_funct_1)).

fof(t62_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3) )
               => ( k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X2)
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t64_tops_2.p',t62_tops_2)).

fof(t63_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t64_tops_2.p',t63_tops_2)).

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
    file('/export/starexec/sandbox/benchmark/tops_2__t64_tops_2.p',redefinition_r2_funct_2)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t64_tops_2.p',d3_struct_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_struct_0(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                    & v2_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t64_tops_2])).

fof(c_0_10,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,X11,X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | k2_relset_1(X11,X12,X13) != X12
      | ~ v2_funct_1(X13)
      | k2_tops_2(X11,X12,X13) = k2_funct_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

fof(c_0_11,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_struct_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0)
    & v2_funct_1(esk3_0)
    & ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X70,X71,X72] :
      ( ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
      | v1_relat_1(X72) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_13,plain,(
    ! [X22,X23,X24] :
      ( ( v1_funct_1(k2_tops_2(X22,X23,X24))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v1_funct_2(k2_tops_2(X22,X23,X24),X23,X22)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( m1_subset_1(k2_tops_2(X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(X23,X22)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).

fof(c_0_14,plain,(
    ! [X64] :
      ( ~ v1_relat_1(X64)
      | ~ v1_funct_1(X64)
      | ~ v2_funct_1(X64)
      | k2_funct_1(k2_funct_1(X64)) = X64 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

cnf(c_0_15,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X58,X59,X60] :
      ( ( k1_relset_1(u1_struct_0(X59),u1_struct_0(X58),k2_tops_2(u1_struct_0(X58),u1_struct_0(X59),X60)) = k2_struct_0(X59)
        | k2_relset_1(u1_struct_0(X58),u1_struct_0(X59),X60) != k2_struct_0(X59)
        | ~ v2_funct_1(X60)
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,u1_struct_0(X58),u1_struct_0(X59))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X59))))
        | v2_struct_0(X59)
        | ~ l1_struct_0(X59)
        | ~ l1_struct_0(X58) )
      & ( k2_relset_1(u1_struct_0(X59),u1_struct_0(X58),k2_tops_2(u1_struct_0(X58),u1_struct_0(X59),X60)) = k2_struct_0(X58)
        | k2_relset_1(u1_struct_0(X58),u1_struct_0(X59),X60) != k2_struct_0(X59)
        | ~ v2_funct_1(X60)
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,u1_struct_0(X58),u1_struct_0(X59))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X59))))
        | v2_struct_0(X59)
        | ~ l1_struct_0(X59)
        | ~ l1_struct_0(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_tops_2])])])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( v1_funct_1(k2_tops_2(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( k2_funct_1(esk3_0) = k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_29,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3)) = k2_struct_0(X2)
    | v2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3) != k2_struct_0(X1)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,plain,
    ( k2_tops_2(X1,X2,k2_tops_2(X2,X1,X3)) = k2_funct_1(k2_tops_2(X2,X1,X3))
    | k2_relset_1(X1,X2,k2_tops_2(X2,X1,X3)) != X2
    | ~ v2_funct_1(k2_tops_2(X2,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_2(X3,X2,X1)
    | ~ v1_funct_1(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( k2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) = esk3_0
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_18]),c_0_20])])).

cnf(c_0_35,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) = k2_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) = esk3_0
    | k2_struct_0(esk1_0) != u1_struct_0(esk1_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_16]),c_0_19]),c_0_20])])).

fof(c_0_38,plain,(
    ! [X61,X62,X63] :
      ( ~ l1_struct_0(X61)
      | ~ l1_struct_0(X62)
      | ~ v1_funct_1(X63)
      | ~ v1_funct_2(X63,u1_struct_0(X61),u1_struct_0(X62))
      | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X61),u1_struct_0(X62))))
      | k2_relset_1(u1_struct_0(X61),u1_struct_0(X62),X63) != k2_struct_0(X62)
      | ~ v2_funct_1(X63)
      | v2_funct_1(k2_tops_2(u1_struct_0(X61),u1_struct_0(X62),X63)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_tops_2])])])).

fof(c_0_39,plain,(
    ! [X34,X35,X36,X37] :
      ( ( ~ r2_funct_2(X34,X35,X36,X37)
        | X36 = X37
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X34,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X34,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X36 != X37
        | r2_funct_2(X34,X35,X36,X37)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X34,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X34,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_40,negated_conjecture,
    ( k2_struct_0(esk1_0) != u1_struct_0(esk1_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0)
    | ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk3_0)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_42,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( k2_struct_0(esk1_0) != u1_struct_0(esk1_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0)
    | ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_17]),c_0_18]),c_0_16]),c_0_19]),c_0_20]),c_0_31]),c_0_30])])).

cnf(c_0_44,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_42])).

fof(c_0_45,plain,(
    ! [X10] :
      ( ~ l1_struct_0(X10)
      | k2_struct_0(X10) = u1_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_46,negated_conjecture,
    ( k2_struct_0(esk1_0) != u1_struct_0(esk1_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_16]),c_0_19]),c_0_20])])).

cnf(c_0_47,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_30])])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_47]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
