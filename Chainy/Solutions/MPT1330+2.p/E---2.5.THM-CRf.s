%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1330+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:04 EST 2020

% Result     : Theorem 9.21s
% Output     : CNFRefutation 9.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 277 expanded)
%              Number of clauses        :   41 ( 111 expanded)
%              Number of leaves         :   14 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  183 (1162 expanded)
%              Number of equality atoms :   62 ( 408 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_tops_2,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_struct_0(X2) = k1_xboole_0
                 => k2_struct_0(X1) = k1_xboole_0 )
               => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2)) = k2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

fof(t132_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | v1_partfun1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT014+2.ax',t132_funct_2)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',d3_struct_0)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k1_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',fc6_relat_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',t38_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',d19_relat_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT014+2.ax',d4_partfun1)).

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t79_relat_1)).

fof(t62_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t62_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t81_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t60_relat_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( l1_struct_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( ( k2_struct_0(X2) = k1_xboole_0
                   => k2_struct_0(X1) = k1_xboole_0 )
                 => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2)) = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_tops_2])).

fof(c_0_15,plain,(
    ! [X5176,X5177,X5178] :
      ( ( X5177 = k1_xboole_0
        | v1_partfun1(X5178,X5176)
        | ~ v1_funct_1(X5178)
        | ~ v1_funct_2(X5178,X5176,X5177)
        | ~ m1_subset_1(X5178,k1_zfmisc_1(k2_zfmisc_1(X5176,X5177)))
        | ~ v1_funct_1(X5178)
        | ~ m1_subset_1(X5178,k1_zfmisc_1(k2_zfmisc_1(X5176,X5177))) )
      & ( X5176 != k1_xboole_0
        | v1_partfun1(X5178,X5176)
        | ~ v1_funct_1(X5178)
        | ~ v1_funct_2(X5178,X5176,X5177)
        | ~ m1_subset_1(X5178,k1_zfmisc_1(k2_zfmisc_1(X5176,X5177)))
        | ~ v1_funct_1(X5178)
        | ~ m1_subset_1(X5178,k1_zfmisc_1(k2_zfmisc_1(X5176,X5177))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

fof(c_0_16,plain,(
    ! [X5896] :
      ( ~ l1_struct_0(X5896)
      | k2_struct_0(X5896) = u1_struct_0(X5896) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_17,negated_conjecture,
    ( l1_struct_0(esk751_0)
    & l1_struct_0(esk752_0)
    & v1_funct_1(esk753_0)
    & v1_funct_2(esk753_0,u1_struct_0(esk751_0),u1_struct_0(esk752_0))
    & m1_subset_1(esk753_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk751_0),u1_struct_0(esk752_0))))
    & ( k2_struct_0(esk752_0) != k1_xboole_0
      | k2_struct_0(esk751_0) = k1_xboole_0 )
    & k8_relset_1(u1_struct_0(esk751_0),u1_struct_0(esk752_0),esk753_0,k2_struct_0(esk752_0)) != k2_struct_0(esk751_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_18,plain,(
    ! [X3679,X3680,X3681] :
      ( ~ m1_subset_1(X3681,k1_zfmisc_1(k2_zfmisc_1(X3679,X3680)))
      | k1_relset_1(X3679,X3680,X3681) = k1_relat_1(X3681) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_19,plain,(
    ! [X3618,X3619,X3620] :
      ( ( v4_relat_1(X3620,X3618)
        | ~ m1_subset_1(X3620,k1_zfmisc_1(k2_zfmisc_1(X3618,X3619))) )
      & ( v5_relat_1(X3620,X3619)
        | ~ m1_subset_1(X3620,k1_zfmisc_1(k2_zfmisc_1(X3618,X3619))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_20,plain,(
    ! [X2097,X2098] :
      ( ~ v1_relat_1(X2097)
      | ~ m1_subset_1(X2098,k1_zfmisc_1(X2097))
      | v1_relat_1(X2098) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_21,plain,(
    ! [X2277,X2278] : v1_relat_1(k2_zfmisc_1(X2277,X2278)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( l1_struct_0(esk752_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( l1_struct_0(esk751_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X3795,X3796,X3797] :
      ( ( k7_relset_1(X3795,X3796,X3797,X3795) = k2_relset_1(X3795,X3796,X3797)
        | ~ m1_subset_1(X3797,k1_zfmisc_1(k2_zfmisc_1(X3795,X3796))) )
      & ( k8_relset_1(X3795,X3796,X3797,X3796) = k1_relset_1(X3795,X3796,X3797)
        | ~ m1_subset_1(X3797,k1_zfmisc_1(k2_zfmisc_1(X3795,X3796))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

cnf(c_0_27,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk753_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk751_0),u1_struct_0(esk752_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_29,plain,(
    ! [X2162,X2163] :
      ( ( ~ v5_relat_1(X2163,X2162)
        | r1_tarski(k2_relat_1(X2163),X2162)
        | ~ v1_relat_1(X2163) )
      & ( ~ r1_tarski(k2_relat_1(X2163),X2162)
        | v5_relat_1(X2163,X2162)
        | ~ v1_relat_1(X2163) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_30,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_33,plain,(
    ! [X4881,X4882] :
      ( ( ~ v1_partfun1(X4882,X4881)
        | k1_relat_1(X4882) = X4881
        | ~ v1_relat_1(X4882)
        | ~ v4_relat_1(X4882,X4881) )
      & ( k1_relat_1(X4882) != X4881
        | v1_partfun1(X4882,X4881)
        | ~ v1_relat_1(X4882)
        | ~ v4_relat_1(X4882,X4881) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk753_0,u1_struct_0(esk751_0),u1_struct_0(esk752_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk753_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk751_0),u1_struct_0(esk752_0),esk753_0,k2_struct_0(esk752_0)) != k2_struct_0(esk751_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( k2_struct_0(esk752_0) = u1_struct_0(esk752_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( k2_struct_0(esk751_0) = u1_struct_0(esk751_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_41,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk751_0),u1_struct_0(esk752_0),esk753_0) = k1_relat_1(esk753_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_43,plain,(
    ! [X2688,X2689] :
      ( ~ v1_relat_1(X2689)
      | ~ r1_tarski(k2_relat_1(X2689),X2688)
      | k5_relat_1(X2689,k6_relat_1(X2688)) = X2689 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

cnf(c_0_44,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,negated_conjecture,
    ( v5_relat_1(esk753_0,u1_struct_0(esk752_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk753_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_32])])).

cnf(c_0_47,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(esk752_0) = k1_xboole_0
    | v1_partfun1(esk753_0,u1_struct_0(esk751_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_28])])).

cnf(c_0_49,negated_conjecture,
    ( v4_relat_1(esk753_0,u1_struct_0(esk751_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk751_0),u1_struct_0(esk752_0),esk753_0,u1_struct_0(esk752_0)) != u1_struct_0(esk751_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk751_0),u1_struct_0(esk752_0),esk753_0,u1_struct_0(esk752_0)) = k1_relat_1(esk753_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_42])).

fof(c_0_52,plain,(
    ! [X2665] :
      ( ( k5_relat_1(k1_xboole_0,X2665) = k1_xboole_0
        | ~ v1_relat_1(X2665) )
      & ( k5_relat_1(X2665,k1_xboole_0) = k1_xboole_0
        | ~ v1_relat_1(X2665) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_relat_1])])])).

cnf(c_0_53,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk753_0),u1_struct_0(esk752_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(esk753_0) = u1_struct_0(esk751_0)
    | u1_struct_0(esk752_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_46])])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(esk753_0) != u1_struct_0(esk751_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k5_relat_1(esk753_0,k6_relat_1(u1_struct_0(esk752_0))) = esk753_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_46])])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk752_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_61,negated_conjecture,
    ( k5_relat_1(esk753_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_46])).

cnf(c_0_62,negated_conjecture,
    ( k2_struct_0(esk751_0) = k1_xboole_0
    | k2_struct_0(esk752_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_63,negated_conjecture,
    ( esk753_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61])).

cnf(c_0_64,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(esk751_0) = k1_xboole_0
    | u1_struct_0(esk752_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_39]),c_0_40])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(esk751_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_63]),c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_59])]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
