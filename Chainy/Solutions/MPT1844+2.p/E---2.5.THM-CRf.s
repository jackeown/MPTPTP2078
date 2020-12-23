%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1844+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:08 EST 2020

% Result     : Theorem 10.69s
% Output     : CNFRefutation 10.69s
% Verified   : 
% Statistics : Number of formulae       :   32 (  52 expanded)
%              Number of clauses        :   17 (  19 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 183 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',fc2_struct_0)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT017+2.ax',dt_k6_domain_1)).

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(cc1_zfmisc_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_zfmisc_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',cc1_zfmisc_1)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(fc6_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v7_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',fc6_struct_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & ~ v7_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t9_tex_2])).

fof(c_0_8,plain,(
    ! [X5932] :
      ( v2_struct_0(X5932)
      | ~ l1_struct_0(X5932)
      | ~ v1_xboole_0(u1_struct_0(X5932)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk1308_0)
    & ~ v7_struct_0(esk1308_0)
    & l1_struct_0(esk1308_0)
    & m1_subset_1(esk1309_0,u1_struct_0(esk1308_0))
    & ~ v1_subset_1(k6_domain_1(u1_struct_0(esk1308_0),esk1309_0),u1_struct_0(esk1308_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X6183,X6184] :
      ( v1_xboole_0(X6183)
      | ~ m1_subset_1(X6184,X6183)
      | m1_subset_1(k6_domain_1(X6183,X6184),k1_zfmisc_1(X6183)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( l1_struct_0(esk1308_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1308_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X11580,X11582] :
      ( ( m1_subset_1(esk1301_1(X11580),X11580)
        | ~ v1_zfmisc_1(X11580)
        | v1_xboole_0(X11580) )
      & ( X11580 = k6_domain_1(X11580,esk1301_1(X11580))
        | ~ v1_zfmisc_1(X11580)
        | v1_xboole_0(X11580) )
      & ( ~ m1_subset_1(X11582,X11580)
        | X11580 != k6_domain_1(X11580,X11582)
        | v1_zfmisc_1(X11580)
        | v1_xboole_0(X11580) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

fof(c_0_15,plain,(
    ! [X989] :
      ( ~ v1_xboole_0(X989)
      | v1_zfmisc_1(X989) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).

fof(c_0_16,plain,(
    ! [X11583,X11584] :
      ( ( ~ v1_subset_1(X11584,X11583)
        | X11584 != X11583
        | ~ m1_subset_1(X11584,k1_zfmisc_1(X11583)) )
      & ( X11584 = X11583
        | v1_subset_1(X11584,X11583)
        | ~ m1_subset_1(X11584,k1_zfmisc_1(X11583)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk1309_0,u1_struct_0(esk1308_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1308_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

fof(c_0_20,plain,(
    ! [X5940] :
      ( v7_struct_0(X5940)
      | ~ l1_struct_0(X5940)
      | ~ v1_zfmisc_1(u1_struct_0(X5940)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).

cnf(c_0_21,plain,
    ( v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2)
    | X2 != k6_domain_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v1_zfmisc_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk1308_0),esk1309_0),k1_zfmisc_1(u1_struct_0(esk1308_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(esk1308_0),esk1309_0),u1_struct_0(esk1308_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,plain,
    ( v7_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_zfmisc_1(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( ~ v7_struct_0(esk1308_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,plain,
    ( v1_zfmisc_1(X1)
    | k6_domain_1(X1,X2) != X1
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1308_0),esk1309_0) = u1_struct_0(esk1308_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_zfmisc_1(u1_struct_0(esk1308_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_12]),c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_18])]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
