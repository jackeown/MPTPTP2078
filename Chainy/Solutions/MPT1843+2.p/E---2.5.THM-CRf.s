%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1843+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:08 EST 2020

% Result     : Theorem 9.37s
% Output     : CNFRefutation 9.37s
% Verified   : 
% Statistics : Number of formulae       :   20 (  36 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :   53 ( 129 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
              & v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

fof(fc7_struct_0,axiom,(
    ! [X1] :
      ( ( v7_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',fc7_struct_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',fc2_struct_0)).

fof(t6_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
                & v7_struct_0(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_tex_2])).

fof(c_0_5,plain,(
    ! [X5942] :
      ( ~ v7_struct_0(X5942)
      | ~ l1_struct_0(X5942)
      | v1_zfmisc_1(u1_struct_0(X5942)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk1308_0)
    & l1_struct_0(esk1308_0)
    & m1_subset_1(esk1309_0,u1_struct_0(esk1308_0))
    & v1_subset_1(k6_domain_1(u1_struct_0(esk1308_0),esk1309_0),u1_struct_0(esk1308_0))
    & v7_struct_0(esk1308_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X5932] :
      ( v2_struct_0(X5932)
      | ~ l1_struct_0(X5932)
      | ~ v1_xboole_0(u1_struct_0(X5932)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_8,plain,(
    ! [X11601,X11602] :
      ( v1_xboole_0(X11601)
      | ~ m1_subset_1(X11602,X11601)
      | ~ v1_subset_1(k6_domain_1(X11601,X11602),X11601)
      | ~ v1_zfmisc_1(X11601) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).

cnf(c_0_9,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( l1_struct_0(esk1308_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v7_struct_0(esk1308_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1308_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk1309_0,u1_struct_0(esk1308_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(esk1308_0),esk1309_0),u1_struct_0(esk1308_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk1308_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_18,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1308_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_10]),c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
