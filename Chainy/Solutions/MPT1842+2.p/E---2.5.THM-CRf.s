%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1842+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:08 EST 2020

% Result     : Theorem 9.80s
% Output     : CNFRefutation 9.80s
% Verified   : 
% Statistics : Number of formulae       :   23 (  36 expanded)
%              Number of clauses        :   12 (  13 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   67 ( 116 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => v1_subset_1(k6_domain_1(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT017+2.ax',dt_k6_domain_1)).

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(cc1_zfmisc_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_zfmisc_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',cc1_zfmisc_1)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v1_xboole_0(X1)
          & ~ v1_zfmisc_1(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => v1_subset_1(k6_domain_1(X1,X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t7_tex_2])).

fof(c_0_6,plain,(
    ! [X6183,X6184] :
      ( v1_xboole_0(X6183)
      | ~ m1_subset_1(X6184,X6183)
      | m1_subset_1(k6_domain_1(X6183,X6184),k1_zfmisc_1(X6183)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v1_xboole_0(esk1306_0)
    & ~ v1_zfmisc_1(esk1306_0)
    & m1_subset_1(esk1307_0,esk1306_0)
    & ~ v1_subset_1(k6_domain_1(esk1306_0,esk1307_0),esk1306_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X11574,X11576] :
      ( ( m1_subset_1(esk1301_1(X11574),X11574)
        | ~ v1_zfmisc_1(X11574)
        | v1_xboole_0(X11574) )
      & ( X11574 = k6_domain_1(X11574,esk1301_1(X11574))
        | ~ v1_zfmisc_1(X11574)
        | v1_xboole_0(X11574) )
      & ( ~ m1_subset_1(X11576,X11574)
        | X11574 != k6_domain_1(X11574,X11576)
        | v1_zfmisc_1(X11574)
        | v1_xboole_0(X11574) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

fof(c_0_9,plain,(
    ! [X989] :
      ( ~ v1_xboole_0(X989)
      | v1_zfmisc_1(X989) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).

fof(c_0_10,plain,(
    ! [X11577,X11578] :
      ( ( ~ v1_subset_1(X11578,X11577)
        | X11578 != X11577
        | ~ m1_subset_1(X11578,k1_zfmisc_1(X11577)) )
      & ( X11578 = X11577
        | v1_subset_1(X11578,X11577)
        | ~ m1_subset_1(X11578,k1_zfmisc_1(X11577)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_11,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk1307_0,esk1306_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( ~ v1_xboole_0(esk1306_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2)
    | X2 != k6_domain_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( v1_zfmisc_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(k6_domain_1(esk1306_0,esk1307_0),k1_zfmisc_1(esk1306_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(esk1306_0,esk1307_0),esk1306_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( v1_zfmisc_1(X1)
    | k6_domain_1(X1,X2) != X1
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k6_domain_1(esk1306_0,esk1307_0) = esk1306_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_zfmisc_1(esk1306_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_12])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
