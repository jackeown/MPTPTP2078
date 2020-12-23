%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t9_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:57 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   34 (  53 expanded)
%              Number of clauses        :   17 (  20 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  104 ( 177 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & ~ v7_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',t9_tex_2)).

fof(cc4_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( ( ~ v1_xboole_0(X2)
              & v1_zfmisc_1(X2) )
           => ( ~ v1_xboole_0(X2)
              & v1_subset_1(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc4_tex_2)).

fof(cc2_subset_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( ~ v1_subset_1(X2,X1)
           => ~ v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc2_subset_1)).

fof(cc1_realset1,axiom,(
    ! [X1] :
      ( ~ v1_zfmisc_1(X1)
     => ~ v1_xboole_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc1_realset1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',dt_k6_domain_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',redefinition_k6_domain_1)).

fof(fc2_zfmisc_1,axiom,(
    ! [X1] : v1_zfmisc_1(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',fc2_zfmisc_1)).

fof(fc6_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v7_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',fc6_struct_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & ~ v7_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t9_tex_2])).

fof(c_0_9,plain,(
    ! [X60,X61] :
      ( ( ~ v1_xboole_0(X61)
        | v1_xboole_0(X61)
        | ~ v1_zfmisc_1(X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(X60))
        | v1_xboole_0(X60)
        | v1_zfmisc_1(X60) )
      & ( v1_subset_1(X61,X60)
        | v1_xboole_0(X61)
        | ~ v1_zfmisc_1(X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(X60))
        | v1_xboole_0(X60)
        | v1_zfmisc_1(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_tex_2])])])])])).

fof(c_0_10,plain,(
    ! [X49,X50] :
      ( v1_xboole_0(X49)
      | ~ m1_subset_1(X50,k1_zfmisc_1(X49))
      | v1_subset_1(X50,X49)
      | ~ v1_xboole_0(X50) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_subset_1])])])])).

fof(c_0_11,plain,(
    ! [X41] :
      ( v1_zfmisc_1(X41)
      | ~ v1_xboole_0(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_realset1])])])).

fof(c_0_12,plain,(
    ! [X112,X113] :
      ( v1_xboole_0(X112)
      | ~ m1_subset_1(X113,X112)
      | m1_subset_1(k6_domain_1(X112,X113),k1_zfmisc_1(X112)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & ~ v7_struct_0(esk1_0)
    & l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ~ v1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_14,plain,
    ( v1_subset_1(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_zfmisc_1(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v1_xboole_0(X1)
    | v1_subset_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v1_zfmisc_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X110,X111] :
      ( v1_xboole_0(X110)
      | ~ m1_subset_1(X111,X110)
      | k6_domain_1(X110,X111) = k1_tarski(X111) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_20,plain,
    ( v1_zfmisc_1(X1)
    | v1_subset_1(X2,X1)
    | ~ v1_zfmisc_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X71] : v1_zfmisc_1(k1_tarski(X71)) ),
    inference(variable_rename,[status(thm)],[fc2_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X120] :
      ( v7_struct_0(X120)
      | ~ l1_struct_0(X120)
      | ~ v1_zfmisc_1(u1_struct_0(X120)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).

cnf(c_0_26,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk1_0))
    | ~ v1_zfmisc_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk2_0) = k1_tarski(esk2_0)
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_28,plain,
    ( v1_zfmisc_1(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( v7_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_zfmisc_1(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])]),c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( ~ v7_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
