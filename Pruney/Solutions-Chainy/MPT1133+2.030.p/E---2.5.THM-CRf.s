%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:25 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  205 (41344739 expanded)
%              Number of clauses        :  165 (16482191 expanded)
%              Number of leaves         :   20 (9861051 expanded)
%              Depth                    :   49
%              Number of atoms          :  758 (297370286 expanded)
%              Number of equality atoms :  146 (35299443 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_pre_topc,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t62_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(rc1_funct_2,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2)
      & v1_funct_1(X3)
      & v1_funct_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(t63_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                   => ( X3 = X4
                     => ( v5_pre_topc(X3,X1,X2)
                      <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t64_pre_topc])).

fof(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))
    & esk6_0 = esk7_0
    & ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
      | ~ v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) )
    & ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
      | v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_22,plain,(
    ! [X37,X38,X39] :
      ( ( v1_funct_1(X39)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | v1_xboole_0(X38) )
      & ( v1_partfun1(X39,X37)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | v1_xboole_0(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X28,X29,X30] :
      ( ( v4_relat_1(X30,X28)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( v5_relat_1(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_27,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | v1_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_28,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_29,plain,(
    ! [X31,X33,X34,X35,X36] :
      ( ( r2_hidden(esk2_1(X31),X31)
        | X31 = k1_xboole_0 )
      & ( ~ r2_hidden(X33,X31)
        | esk2_1(X31) != k4_mcart_1(X33,X34,X35,X36)
        | X31 = k1_xboole_0 )
      & ( ~ r2_hidden(X34,X31)
        | esk2_1(X31) != k4_mcart_1(X33,X34,X35,X36)
        | X31 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

fof(c_0_30,plain,(
    ! [X40,X41] :
      ( ( ~ v1_partfun1(X41,X40)
        | k1_relat_1(X41) = X40
        | ~ v1_relat_1(X41)
        | ~ v4_relat_1(X41,X40) )
      & ( k1_relat_1(X41) != X40
        | v1_partfun1(X41,X40)
        | ~ v1_relat_1(X41)
        | ~ v4_relat_1(X41,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_31,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( v1_partfun1(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_43,negated_conjecture,
    ( v4_relat_1(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( v1_partfun1(esk6_0,u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_37]),c_0_38]),c_0_34])])).

cnf(c_0_46,negated_conjecture,
    ( v4_relat_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_37])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(esk6_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44])])).

fof(c_0_49,plain,(
    ! [X22,X23,X24] :
      ( ~ r2_hidden(X22,X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X24))
      | ~ v1_xboole_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(esk6_0) = u1_struct_0(esk4_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_45]),c_0_46]),c_0_44])])).

cnf(c_0_51,negated_conjecture,
    ( k1_relat_1(esk6_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_52,plain,(
    ! [X14,X15] :
      ( ( k2_zfmisc_1(X14,X15) != k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_32])).

cnf(c_0_57,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) = k1_xboole_0
    | u1_struct_0(esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_54])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_59,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_60,plain,(
    ! [X49,X50,X51,X52] :
      ( ( ~ v5_pre_topc(X51,X49,X50)
        | v5_pre_topc(X52,g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49)),X50)
        | X51 != X52
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49))),u1_struct_0(X50))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49))),u1_struct_0(X50))))
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50))))
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) )
      & ( ~ v5_pre_topc(X52,g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49)),X50)
        | v5_pre_topc(X51,X49,X50)
        | X51 != X52
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49))),u1_struct_0(X50))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49))),u1_struct_0(X50))))
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50))))
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_59])])).

cnf(c_0_62,plain,
    ( v5_pre_topc(X4,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | X4 != X1
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_40])).

cnf(c_0_64,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_67,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_68,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_63])).

fof(c_0_69,plain,(
    ! [X48] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48)))
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48)))
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

fof(c_0_70,plain,(
    ! [X45,X46] :
      ( ( v1_pre_topc(g1_pre_topc(X45,X46))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k1_zfmisc_1(X45))) )
      & ( l1_pre_topc(g1_pre_topc(X45,X46))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k1_zfmisc_1(X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

fof(c_0_71,plain,(
    ! [X47] :
      ( ~ l1_pre_topc(X47)
      | m1_subset_1(u1_pre_topc(X47),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X47)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_72,plain,(
    ! [X42,X43] :
      ( m1_subset_1(esk3_2(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      & v1_relat_1(esk3_2(X42,X43))
      & v4_relat_1(esk3_2(X42,X43),X42)
      & v5_relat_1(esk3_2(X42,X43),X43)
      & v1_funct_1(esk3_2(X42,X43))
      & v1_funct_2(esk3_2(X42,X43),X42,X43) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).

fof(c_0_73,plain,(
    ! [X53,X54,X55,X56] :
      ( ( ~ v5_pre_topc(X55,X53,X54)
        | v5_pre_topc(X56,X53,g1_pre_topc(u1_struct_0(X54),u1_pre_topc(X54)))
        | X55 != X56
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,u1_struct_0(X53),u1_struct_0(g1_pre_topc(u1_struct_0(X54),u1_pre_topc(X54))))
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(g1_pre_topc(u1_struct_0(X54),u1_pre_topc(X54))))))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54))))
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54)
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53) )
      & ( ~ v5_pre_topc(X56,X53,g1_pre_topc(u1_struct_0(X54),u1_pre_topc(X54)))
        | v5_pre_topc(X55,X53,X54)
        | X55 != X56
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,u1_struct_0(X53),u1_struct_0(g1_pre_topc(u1_struct_0(X54),u1_pre_topc(X54))))
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(g1_pre_topc(u1_struct_0(X54),u1_pre_topc(X54))))))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54))))
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54)
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67]),c_0_33]),c_0_34]),c_0_32])]),c_0_68])).

cnf(c_0_75,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_77,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_78,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_80,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_81,plain,
    ( v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | X1 != X4
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_82,plain,
    ( v5_pre_topc(X4,X2,X3)
    | ~ v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | X4 != X1
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_77])])).

cnf(c_0_84,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_86,plain,
    ( ~ r2_hidden(X1,esk3_2(X2,X3))
    | ~ v1_xboole_0(k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_80])).

cnf(c_0_87,plain,
    ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_88,plain,
    ( v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v5_pre_topc(X1,X2,X3)
    | X1 != X4
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_89,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_77])])).

cnf(c_0_91,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_85,c_0_24])).

cnf(c_0_92,plain,
    ( ~ r2_hidden(X1,esk3_2(X2,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_58]),c_0_59])])).

fof(c_0_93,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_94,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_65]),c_0_66]),c_0_67]),c_0_33]),c_0_34]),c_0_32])]),c_0_68])).

cnf(c_0_95,plain,
    ( v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_38]),c_0_76]),c_0_66]),c_0_77]),c_0_67]),c_0_34]),c_0_37])])).

cnf(c_0_97,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_99,plain,
    ( v1_funct_2(esk3_2(X1,X2),X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_100,plain,
    ( v1_funct_1(esk3_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_101,plain,
    ( esk3_2(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_92,c_0_40])).

fof(c_0_102,plain,(
    ! [X16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_103,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_104,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_105,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_75]),c_0_76]),c_0_77])])).

cnf(c_0_106,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_38]),c_0_76]),c_0_66]),c_0_77]),c_0_67]),c_0_34]),c_0_37])])).

cnf(c_0_107,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_68]),c_0_65])).

cnf(c_0_108,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_98,c_0_24])).

cnf(c_0_109,plain,
    ( v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),X1,X2)
    | ~ v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_99]),c_0_100]),c_0_80])])).

cnf(c_0_110,plain,
    ( v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_101])).

cnf(c_0_111,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_112,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(esk6_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_37])).

cnf(c_0_114,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_84]),c_0_77])])).

cnf(c_0_115,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_68]),c_0_65])).

cnf(c_0_116,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_107])).

fof(c_0_117,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_118,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_57]),c_0_101]),c_0_101]),c_0_101]),c_0_110]),c_0_101]),c_0_58]),c_0_111])])).

cnf(c_0_119,negated_conjecture,
    ( k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)) = esk6_0
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_120,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_116])).

cnf(c_0_121,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_122,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_75]),c_0_76]),c_0_77])])).

cnf(c_0_123,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_58]),c_0_58]),c_0_121])])).

cnf(c_0_124,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_84]),c_0_77])])).

cnf(c_0_125,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_123]),c_0_123])).

cnf(c_0_126,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_123]),c_0_123]),c_0_123]),c_0_123]),c_0_111])])).

cnf(c_0_127,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_66]),c_0_67])])).

cnf(c_0_128,plain,
    ( v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_99]),c_0_100]),c_0_80])])).

cnf(c_0_129,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_130,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_57]),c_0_101]),c_0_101]),c_0_101]),c_0_110]),c_0_101]),c_0_58]),c_0_111])])).

cnf(c_0_131,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_123]),c_0_123]),c_0_123]),c_0_123]),c_0_111])])).

cnf(c_0_132,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_57]),c_0_110])])).

cnf(c_0_133,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_134,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_75]),c_0_76]),c_0_77])])).

cnf(c_0_135,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_123]),c_0_123])).

cnf(c_0_137,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_133])).

cnf(c_0_138,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_84]),c_0_77])])).

cnf(c_0_139,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_57]),c_0_110])])).

cnf(c_0_140,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_136,c_0_132])).

cnf(c_0_141,plain,
    ( ~ r2_hidden(X1,esk3_2(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_137]),c_0_59])])).

cnf(c_0_142,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_123])).

cnf(c_0_143,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_139]),c_0_66]),c_0_67])]),c_0_140])).

cnf(c_0_144,plain,
    ( esk3_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_141,c_0_40])).

cnf(c_0_145,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_142,c_0_143])).

cnf(c_0_146,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_144])).

cnf(c_0_147,plain,
    ( v1_partfun1(X1,X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_148,plain,
    ( v1_partfun1(esk3_2(X1,X2),X1)
    | v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_80]),c_0_99]),c_0_100])])).

cnf(c_0_149,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_145]),c_0_66]),c_0_67]),c_0_142]),c_0_146]),c_0_111]),c_0_111])])).

cnf(c_0_150,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_147])).

cnf(c_0_151,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_111])).

cnf(c_0_152,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_111])).

cnf(c_0_153,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_148,c_0_144])).

cnf(c_0_154,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_75]),c_0_76]),c_0_77])])).

cnf(c_0_155,plain,
    ( v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_151]),c_0_152])])).

cnf(c_0_156,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_153])).

cnf(c_0_157,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_84]),c_0_77])])).

cnf(c_0_158,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_155,c_0_156])).

cnf(c_0_159,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_145]),c_0_66]),c_0_67]),c_0_142]),c_0_146]),c_0_111]),c_0_111])])).

cnf(c_0_160,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_157,c_0_125])).

cnf(c_0_161,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_158]),c_0_151]),c_0_152])])).

cnf(c_0_162,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_75]),c_0_76]),c_0_77])])).

cnf(c_0_163,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_160]),c_0_145])).

cnf(c_0_164,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_123]),c_0_161])).

cnf(c_0_165,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_84]),c_0_77])])).

cnf(c_0_166,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_163]),c_0_145])).

cnf(c_0_167,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_136,c_0_163])).

cnf(c_0_168,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_38]),c_0_76]),c_0_66]),c_0_77]),c_0_67]),c_0_34]),c_0_37])])).

cnf(c_0_169,plain,
    ( v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),X1,X2)
    | ~ v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_99]),c_0_100]),c_0_80])])).

cnf(c_0_170,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | u1_struct_0(esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_164])).

cnf(c_0_171,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_166]),c_0_167])).

cnf(c_0_172,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_168,c_0_123]),c_0_123]),c_0_123]),c_0_123]),c_0_111])])).

cnf(c_0_173,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,X1,esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_170]),c_0_101]),c_0_101]),c_0_76]),c_0_77]),c_0_101]),c_0_101]),c_0_111])])).

cnf(c_0_174,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))
    | v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_125,c_0_171])).

cnf(c_0_175,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_142,c_0_171])).

cnf(c_0_176,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_172,c_0_171]),c_0_110])])).

cnf(c_0_177,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_174]),c_0_175])]),c_0_176])).

cnf(c_0_178,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_75]),c_0_66]),c_0_67])])).

cnf(c_0_179,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,X1,esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk5_0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_171]),c_0_101]),c_0_101]),c_0_76]),c_0_77]),c_0_101]),c_0_110]),c_0_101]),c_0_58]),c_0_111])])).

cnf(c_0_180,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_84]),c_0_67])])).

cnf(c_0_181,plain,
    ( v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_99]),c_0_100]),c_0_80])])).

cnf(c_0_182,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_136,c_0_171])).

cnf(c_0_183,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_180]),c_0_66]),c_0_67])])).

cnf(c_0_184,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,X1,esk5_0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_170]),c_0_101]),c_0_101]),c_0_76]),c_0_77]),c_0_101]),c_0_101]),c_0_111])])).

cnf(c_0_185,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_182,c_0_183])).

cnf(c_0_186,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_180]),c_0_175])]),c_0_185])).

cnf(c_0_187,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_38]),c_0_76]),c_0_66]),c_0_77]),c_0_67]),c_0_34]),c_0_37])])).

cnf(c_0_188,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_75]),c_0_66]),c_0_67])])).

cnf(c_0_189,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_187,c_0_123]),c_0_123]),c_0_123]),c_0_123]),c_0_111])])).

cnf(c_0_190,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188,c_0_84]),c_0_67])])).

cnf(c_0_191,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_189,c_0_171]),c_0_110])])).

cnf(c_0_192,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,X1,esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_171]),c_0_101]),c_0_101]),c_0_76]),c_0_77]),c_0_101]),c_0_101]),c_0_111])])).

cnf(c_0_193,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))
    | v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_174,c_0_190])).

cnf(c_0_194,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_190]),c_0_66]),c_0_67])])).

cnf(c_0_195,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_190]),c_0_67])])).

cnf(c_0_196,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_175,c_0_190])).

cnf(c_0_197,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_176,c_0_190])).

cnf(c_0_198,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0)),esk5_0) ),
    inference(rw,[status(thm)],[c_0_191,c_0_190])).

cnf(c_0_199,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0)),esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_193]),c_0_194]),c_0_195]),c_0_196])]),c_0_197])).

cnf(c_0_200,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_182,c_0_190])).

cnf(c_0_201,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_198,c_0_199])])).

cnf(c_0_202,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,X1,esk5_0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_171]),c_0_101]),c_0_101]),c_0_76]),c_0_77]),c_0_101]),c_0_101]),c_0_111])])).

cnf(c_0_203,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_200,c_0_201])])).

cnf(c_0_204,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202,c_0_199]),c_0_194]),c_0_195]),c_0_196])]),c_0_203]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.60/0.81  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.60/0.81  # and selection function SelectNewComplexAHPNS.
% 0.60/0.81  #
% 0.60/0.81  # Preprocessing time       : 0.032 s
% 0.60/0.81  # Presaturation interreduction done
% 0.60/0.81  
% 0.60/0.81  # Proof found!
% 0.60/0.81  # SZS status Theorem
% 0.60/0.81  # SZS output start CNFRefutation
% 0.60/0.81  fof(t64_pre_topc, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_pre_topc)).
% 0.60/0.81  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.60/0.81  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.60/0.81  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.60/0.81  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.60/0.81  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 0.60/0.81  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.60/0.81  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.60/0.81  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.60/0.81  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.60/0.81  fof(t62_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 0.60/0.81  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.60/0.81  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.60/0.81  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.60/0.81  fof(rc1_funct_2, axiom, ![X1, X2]:?[X3]:(((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&v1_relat_1(X3))&v4_relat_1(X3,X1))&v5_relat_1(X3,X2))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 0.60/0.81  fof(t63_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_pre_topc)).
% 0.60/0.81  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.60/0.81  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.60/0.81  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.60/0.81  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.60/0.81  fof(c_0_20, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))))), inference(assume_negation,[status(cth)],[t64_pre_topc])).
% 0.60/0.81  fof(c_0_21, negated_conjecture, ((v2_pre_topc(esk4_0)&l1_pre_topc(esk4_0))&((v2_pre_topc(esk5_0)&l1_pre_topc(esk5_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))))&(esk6_0=esk7_0&((~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))&(v5_pre_topc(esk6_0,esk4_0,esk5_0)|v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.60/0.81  fof(c_0_22, plain, ![X37, X38, X39]:((v1_funct_1(X39)|(~v1_funct_1(X39)|~v1_funct_2(X39,X37,X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|v1_xboole_0(X38))&(v1_partfun1(X39,X37)|(~v1_funct_1(X39)|~v1_funct_2(X39,X37,X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|v1_xboole_0(X38))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.60/0.81  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_24, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  fof(c_0_26, plain, ![X28, X29, X30]:((v4_relat_1(X30,X28)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))&(v5_relat_1(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.60/0.81  fof(c_0_27, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|v1_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.60/0.81  fof(c_0_28, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.60/0.81  fof(c_0_29, plain, ![X31, X33, X34, X35, X36]:((r2_hidden(esk2_1(X31),X31)|X31=k1_xboole_0)&((~r2_hidden(X33,X31)|esk2_1(X31)!=k4_mcart_1(X33,X34,X35,X36)|X31=k1_xboole_0)&(~r2_hidden(X34,X31)|esk2_1(X31)!=k4_mcart_1(X33,X34,X35,X36)|X31=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 0.60/0.81  fof(c_0_30, plain, ![X40, X41]:((~v1_partfun1(X41,X40)|k1_relat_1(X41)=X40|(~v1_relat_1(X41)|~v4_relat_1(X41,X40)))&(k1_relat_1(X41)!=X40|v1_partfun1(X41,X40)|(~v1_relat_1(X41)|~v4_relat_1(X41,X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.60/0.81  cnf(c_0_31, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.60/0.81  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.60/0.81  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 0.60/0.81  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_35, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.60/0.81  cnf(c_0_36, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.60/0.81  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_39, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.60/0.81  cnf(c_0_40, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.60/0.81  cnf(c_0_41, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.60/0.81  cnf(c_0_42, negated_conjecture, (v1_partfun1(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))|v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])])).
% 0.60/0.81  cnf(c_0_43, negated_conjecture, (v4_relat_1(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))), inference(spm,[status(thm)],[c_0_35, c_0_32])).
% 0.60/0.81  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.60/0.81  cnf(c_0_45, negated_conjecture, (v1_partfun1(esk6_0,u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_37]), c_0_38]), c_0_34])])).
% 0.60/0.81  cnf(c_0_46, negated_conjecture, (v4_relat_1(esk6_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_35, c_0_37])).
% 0.60/0.81  cnf(c_0_47, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.60/0.81  cnf(c_0_48, negated_conjecture, (k1_relat_1(esk6_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44])])).
% 0.60/0.81  fof(c_0_49, plain, ![X22, X23, X24]:(~r2_hidden(X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(X24))|~v1_xboole_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.60/0.81  cnf(c_0_50, negated_conjecture, (k1_relat_1(esk6_0)=u1_struct_0(esk4_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_45]), c_0_46]), c_0_44])])).
% 0.60/0.81  cnf(c_0_51, negated_conjecture, (k1_relat_1(esk6_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.60/0.81  fof(c_0_52, plain, ![X14, X15]:((k2_zfmisc_1(X14,X15)!=k1_xboole_0|(X14=k1_xboole_0|X15=k1_xboole_0))&((X14!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0)&(X15!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.60/0.81  cnf(c_0_53, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.60/0.81  cnf(c_0_54, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))=k1_xboole_0|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.60/0.81  cnf(c_0_55, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.60/0.81  cnf(c_0_56, negated_conjecture, (~r2_hidden(X1,esk6_0)|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))), inference(spm,[status(thm)],[c_0_53, c_0_32])).
% 0.60/0.81  cnf(c_0_57, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))=k1_xboole_0|u1_struct_0(esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_54])).
% 0.60/0.81  cnf(c_0_58, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_55])).
% 0.60/0.81  cnf(c_0_59, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.60/0.81  fof(c_0_60, plain, ![X49, X50, X51, X52]:((~v5_pre_topc(X51,X49,X50)|v5_pre_topc(X52,g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49)),X50)|X51!=X52|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49))),u1_struct_0(X50))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49))),u1_struct_0(X50)))))|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50)))))|(~v2_pre_topc(X50)|~l1_pre_topc(X50))|(~v2_pre_topc(X49)|~l1_pre_topc(X49)))&(~v5_pre_topc(X52,g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49)),X50)|v5_pre_topc(X51,X49,X50)|X51!=X52|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49))),u1_struct_0(X50))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49))),u1_struct_0(X50)))))|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50)))))|(~v2_pre_topc(X50)|~l1_pre_topc(X50))|(~v2_pre_topc(X49)|~l1_pre_topc(X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).
% 0.60/0.81  cnf(c_0_61, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_59])])).
% 0.60/0.81  cnf(c_0_62, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.60/0.81  cnf(c_0_63, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_40])).
% 0.60/0.81  cnf(c_0_64, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_62])).
% 0.60/0.81  cnf(c_0_65, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|esk6_0=k1_xboole_0|v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(spm,[status(thm)],[c_0_33, c_0_63])).
% 0.60/0.81  cnf(c_0_66, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_67, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_68, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|esk6_0=k1_xboole_0|m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(spm,[status(thm)],[c_0_32, c_0_63])).
% 0.60/0.81  fof(c_0_69, plain, ![X48]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48)))|(~v2_pre_topc(X48)|~l1_pre_topc(X48)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48)))|(~v2_pre_topc(X48)|~l1_pre_topc(X48)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.60/0.81  fof(c_0_70, plain, ![X45, X46]:((v1_pre_topc(g1_pre_topc(X45,X46))|~m1_subset_1(X46,k1_zfmisc_1(k1_zfmisc_1(X45))))&(l1_pre_topc(g1_pre_topc(X45,X46))|~m1_subset_1(X46,k1_zfmisc_1(k1_zfmisc_1(X45))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.60/0.81  fof(c_0_71, plain, ![X47]:(~l1_pre_topc(X47)|m1_subset_1(u1_pre_topc(X47),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X47))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.60/0.81  fof(c_0_72, plain, ![X42, X43]:(((((m1_subset_1(esk3_2(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X42,X43)))&v1_relat_1(esk3_2(X42,X43)))&v4_relat_1(esk3_2(X42,X43),X42))&v5_relat_1(esk3_2(X42,X43),X43))&v1_funct_1(esk3_2(X42,X43)))&v1_funct_2(esk3_2(X42,X43),X42,X43)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).
% 0.60/0.81  fof(c_0_73, plain, ![X53, X54, X55, X56]:((~v5_pre_topc(X55,X53,X54)|v5_pre_topc(X56,X53,g1_pre_topc(u1_struct_0(X54),u1_pre_topc(X54)))|X55!=X56|(~v1_funct_1(X56)|~v1_funct_2(X56,u1_struct_0(X53),u1_struct_0(g1_pre_topc(u1_struct_0(X54),u1_pre_topc(X54))))|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(g1_pre_topc(u1_struct_0(X54),u1_pre_topc(X54)))))))|(~v1_funct_1(X55)|~v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54)))))|(~v2_pre_topc(X54)|~l1_pre_topc(X54))|(~v2_pre_topc(X53)|~l1_pre_topc(X53)))&(~v5_pre_topc(X56,X53,g1_pre_topc(u1_struct_0(X54),u1_pre_topc(X54)))|v5_pre_topc(X55,X53,X54)|X55!=X56|(~v1_funct_1(X56)|~v1_funct_2(X56,u1_struct_0(X53),u1_struct_0(g1_pre_topc(u1_struct_0(X54),u1_pre_topc(X54))))|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(g1_pre_topc(u1_struct_0(X54),u1_pre_topc(X54)))))))|(~v1_funct_1(X55)|~v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54)))))|(~v2_pre_topc(X54)|~l1_pre_topc(X54))|(~v2_pre_topc(X53)|~l1_pre_topc(X53)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).
% 0.60/0.81  cnf(c_0_74, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|esk6_0=k1_xboole_0|v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_67]), c_0_33]), c_0_34]), c_0_32])]), c_0_68])).
% 0.60/0.81  cnf(c_0_75, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.60/0.81  cnf(c_0_76, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_77, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_78, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.60/0.81  cnf(c_0_79, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.60/0.81  cnf(c_0_80, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.60/0.81  cnf(c_0_81, plain, (v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.60/0.81  cnf(c_0_82, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.60/0.81  cnf(c_0_83, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|esk6_0=k1_xboole_0|v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_77])])).
% 0.60/0.81  cnf(c_0_84, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.60/0.81  cnf(c_0_85, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk5_0)|v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_86, plain, (~r2_hidden(X1,esk3_2(X2,X3))|~v1_xboole_0(k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_53, c_0_80])).
% 0.60/0.81  cnf(c_0_87, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_81])).
% 0.60/0.81  cnf(c_0_88, plain, (v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.60/0.81  cnf(c_0_89, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_82])).
% 0.60/0.81  cnf(c_0_90, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|esk6_0=k1_xboole_0|v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_77])])).
% 0.60/0.81  cnf(c_0_91, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_85, c_0_24])).
% 0.60/0.81  cnf(c_0_92, plain, (~r2_hidden(X1,esk3_2(X2,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_58]), c_0_59])])).
% 0.60/0.81  fof(c_0_93, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.60/0.81  cnf(c_0_94, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|esk6_0=k1_xboole_0|v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_65]), c_0_66]), c_0_67]), c_0_33]), c_0_34]), c_0_32])]), c_0_68])).
% 0.60/0.81  cnf(c_0_95, plain, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_88])).
% 0.60/0.81  cnf(c_0_96, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_38]), c_0_76]), c_0_66]), c_0_77]), c_0_67]), c_0_34]), c_0_37])])).
% 0.60/0.81  cnf(c_0_97, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|esk6_0=k1_xboole_0|v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.60/0.81  cnf(c_0_98, negated_conjecture, (~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_99, plain, (v1_funct_2(esk3_2(X1,X2),X1,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.60/0.81  cnf(c_0_100, plain, (v1_funct_1(esk3_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.60/0.81  cnf(c_0_101, plain, (esk3_2(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_92, c_0_40])).
% 0.60/0.81  fof(c_0_102, plain, ![X16]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.60/0.81  fof(c_0_103, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.60/0.81  cnf(c_0_104, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.60/0.81  cnf(c_0_105, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|esk6_0=k1_xboole_0|v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_75]), c_0_76]), c_0_77])])).
% 0.60/0.81  cnf(c_0_106, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_38]), c_0_76]), c_0_66]), c_0_77]), c_0_67]), c_0_34]), c_0_37])])).
% 0.60/0.81  cnf(c_0_107, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|esk6_0=k1_xboole_0|v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_68]), c_0_65])).
% 0.60/0.81  cnf(c_0_108, negated_conjecture, (~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_98, c_0_24])).
% 0.60/0.81  cnf(c_0_109, plain, (v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),X1,X2)|~v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v1_funct_2(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))|~m1_subset_1(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_99]), c_0_100]), c_0_80])])).
% 0.60/0.81  cnf(c_0_110, plain, (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_99, c_0_101])).
% 0.60/0.81  cnf(c_0_111, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.60/0.81  cnf(c_0_112, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.60/0.81  cnf(c_0_113, negated_conjecture, (r1_tarski(esk6_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_104, c_0_37])).
% 0.60/0.81  cnf(c_0_114, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|esk6_0=k1_xboole_0|v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_84]), c_0_77])])).
% 0.60/0.81  cnf(c_0_115, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|esk6_0=k1_xboole_0|v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_68]), c_0_65])).
% 0.60/0.81  cnf(c_0_116, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|esk6_0=k1_xboole_0|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_108, c_0_107])).
% 0.60/0.81  fof(c_0_117, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.60/0.81  cnf(c_0_118, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_57]), c_0_101]), c_0_101]), c_0_101]), c_0_110]), c_0_101]), c_0_58]), c_0_111])])).
% 0.60/0.81  cnf(c_0_119, negated_conjecture, (k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))=esk6_0|~r1_tarski(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)),esk6_0)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.60/0.81  cnf(c_0_120, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_116])).
% 0.60/0.81  cnf(c_0_121, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_117])).
% 0.60/0.81  cnf(c_0_122, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_75]), c_0_76]), c_0_77])])).
% 0.60/0.81  cnf(c_0_123, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_58]), c_0_58]), c_0_121])])).
% 0.60/0.81  cnf(c_0_124, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_84]), c_0_77])])).
% 0.60/0.81  cnf(c_0_125, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_123]), c_0_123])).
% 0.60/0.81  cnf(c_0_126, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_123]), c_0_123]), c_0_123]), c_0_123]), c_0_111])])).
% 0.60/0.81  cnf(c_0_127, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_66]), c_0_67])])).
% 0.60/0.81  cnf(c_0_128, plain, (v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),X1,X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v1_funct_2(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))|~m1_subset_1(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_99]), c_0_100]), c_0_80])])).
% 0.60/0.81  cnf(c_0_129, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 0.60/0.81  cnf(c_0_130, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_57]), c_0_101]), c_0_101]), c_0_101]), c_0_110]), c_0_101]), c_0_58]), c_0_111])])).
% 0.60/0.81  cnf(c_0_131, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_123]), c_0_123]), c_0_123]), c_0_123]), c_0_111])])).
% 0.60/0.81  cnf(c_0_132, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_57]), c_0_110])])).
% 0.60/0.81  cnf(c_0_133, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.60/0.81  cnf(c_0_134, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_75]), c_0_76]), c_0_77])])).
% 0.60/0.81  cnf(c_0_135, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(spm,[status(thm)],[c_0_131, c_0_132])).
% 0.60/0.81  cnf(c_0_136, negated_conjecture, (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_123]), c_0_123])).
% 0.60/0.81  cnf(c_0_137, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_133])).
% 0.60/0.81  cnf(c_0_138, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_84]), c_0_77])])).
% 0.60/0.81  cnf(c_0_139, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_57]), c_0_110])])).
% 0.60/0.81  cnf(c_0_140, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_136, c_0_132])).
% 0.60/0.81  cnf(c_0_141, plain, (~r2_hidden(X1,esk3_2(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_137]), c_0_59])])).
% 0.60/0.81  cnf(c_0_142, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(rw,[status(thm)],[c_0_33, c_0_123])).
% 0.60/0.81  cnf(c_0_143, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_139]), c_0_66]), c_0_67])]), c_0_140])).
% 0.60/0.81  cnf(c_0_144, plain, (esk3_2(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_141, c_0_40])).
% 0.60/0.81  cnf(c_0_145, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(spm,[status(thm)],[c_0_142, c_0_143])).
% 0.60/0.81  cnf(c_0_146, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_100, c_0_144])).
% 0.60/0.81  cnf(c_0_147, plain, (v1_partfun1(X1,X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.60/0.81  cnf(c_0_148, plain, (v1_partfun1(esk3_2(X1,X2),X1)|v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_80]), c_0_99]), c_0_100])])).
% 0.60/0.81  cnf(c_0_149, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_145]), c_0_66]), c_0_67]), c_0_142]), c_0_146]), c_0_111]), c_0_111])])).
% 0.60/0.81  cnf(c_0_150, plain, (v1_partfun1(X1,k1_relat_1(X1))|~v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_147])).
% 0.60/0.81  cnf(c_0_151, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_111])).
% 0.60/0.81  cnf(c_0_152, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_111])).
% 0.60/0.81  cnf(c_0_153, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_148, c_0_144])).
% 0.60/0.81  cnf(c_0_154, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_75]), c_0_76]), c_0_77])])).
% 0.60/0.81  cnf(c_0_155, plain, (v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_151]), c_0_152])])).
% 0.60/0.81  cnf(c_0_156, plain, (X1=k1_xboole_0|v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_153])).
% 0.60/0.81  cnf(c_0_157, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_84]), c_0_77])])).
% 0.60/0.81  cnf(c_0_158, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_155, c_0_156])).
% 0.60/0.81  cnf(c_0_159, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_145]), c_0_66]), c_0_67]), c_0_142]), c_0_146]), c_0_111]), c_0_111])])).
% 0.60/0.81  cnf(c_0_160, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_157, c_0_125])).
% 0.60/0.81  cnf(c_0_161, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_158]), c_0_151]), c_0_152])])).
% 0.60/0.81  cnf(c_0_162, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_75]), c_0_76]), c_0_77])])).
% 0.60/0.81  cnf(c_0_163, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_160]), c_0_145])).
% 0.60/0.81  cnf(c_0_164, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|v1_xboole_0(u1_struct_0(esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_123]), c_0_161])).
% 0.60/0.81  cnf(c_0_165, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_84]), c_0_77])])).
% 0.60/0.81  cnf(c_0_166, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_163]), c_0_145])).
% 0.60/0.81  cnf(c_0_167, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_136, c_0_163])).
% 0.60/0.81  cnf(c_0_168, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_38]), c_0_76]), c_0_66]), c_0_77]), c_0_67]), c_0_34]), c_0_37])])).
% 0.60/0.81  cnf(c_0_169, plain, (v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),X1,X2)|~v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v1_funct_2(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))|~m1_subset_1(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_99]), c_0_100]), c_0_80])])).
% 0.60/0.81  cnf(c_0_170, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|u1_struct_0(esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_164])).
% 0.60/0.81  cnf(c_0_171, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_166]), c_0_167])).
% 0.60/0.81  cnf(c_0_172, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_168, c_0_123]), c_0_123]), c_0_123]), c_0_123]), c_0_111])])).
% 0.60/0.81  cnf(c_0_173, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,X1,esk5_0)|~v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_170]), c_0_101]), c_0_101]), c_0_76]), c_0_77]), c_0_101]), c_0_101]), c_0_111])])).
% 0.60/0.81  cnf(c_0_174, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))|v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_125, c_0_171])).
% 0.60/0.81  cnf(c_0_175, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))))), inference(rw,[status(thm)],[c_0_142, c_0_171])).
% 0.60/0.81  cnf(c_0_176, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_172, c_0_171]), c_0_110])])).
% 0.60/0.81  cnf(c_0_177, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_174]), c_0_175])]), c_0_176])).
% 0.60/0.81  cnf(c_0_178, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177, c_0_75]), c_0_66]), c_0_67])])).
% 0.60/0.81  cnf(c_0_179, negated_conjecture, (v5_pre_topc(k1_xboole_0,X1,esk5_0)|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk5_0)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_171]), c_0_101]), c_0_101]), c_0_76]), c_0_77]), c_0_101]), c_0_110]), c_0_101]), c_0_58]), c_0_111])])).
% 0.60/0.81  cnf(c_0_180, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_84]), c_0_67])])).
% 0.60/0.81  cnf(c_0_181, plain, (v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),X1,X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v1_funct_2(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))|~m1_subset_1(esk3_2(u1_struct_0(X1),u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_99]), c_0_100]), c_0_80])])).
% 0.60/0.81  cnf(c_0_182, negated_conjecture, (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_136, c_0_171])).
% 0.60/0.81  cnf(c_0_183, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_180]), c_0_66]), c_0_67])])).
% 0.60/0.81  cnf(c_0_184, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,X1,esk5_0)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_170]), c_0_101]), c_0_101]), c_0_76]), c_0_77]), c_0_101]), c_0_101]), c_0_111])])).
% 0.60/0.81  cnf(c_0_185, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_182, c_0_183])).
% 0.60/0.81  cnf(c_0_186, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184, c_0_180]), c_0_175])]), c_0_185])).
% 0.60/0.81  cnf(c_0_187, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_38]), c_0_76]), c_0_66]), c_0_77]), c_0_67]), c_0_34]), c_0_37])])).
% 0.60/0.81  cnf(c_0_188, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186, c_0_75]), c_0_66]), c_0_67])])).
% 0.60/0.81  cnf(c_0_189, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_187, c_0_123]), c_0_123]), c_0_123]), c_0_123]), c_0_111])])).
% 0.60/0.81  cnf(c_0_190, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188, c_0_84]), c_0_67])])).
% 0.60/0.81  cnf(c_0_191, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_189, c_0_171]), c_0_110])])).
% 0.60/0.81  cnf(c_0_192, negated_conjecture, (v5_pre_topc(k1_xboole_0,X1,esk5_0)|~v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_171]), c_0_101]), c_0_101]), c_0_76]), c_0_77]), c_0_101]), c_0_101]), c_0_111])])).
% 0.60/0.81  cnf(c_0_193, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))|v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_174, c_0_190])).
% 0.60/0.81  cnf(c_0_194, negated_conjecture, (v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_190]), c_0_66]), c_0_67])])).
% 0.60/0.81  cnf(c_0_195, negated_conjecture, (l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_190]), c_0_67])])).
% 0.60/0.81  cnf(c_0_196, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))))), inference(rw,[status(thm)],[c_0_175, c_0_190])).
% 0.60/0.81  cnf(c_0_197, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_176, c_0_190])).
% 0.60/0.81  cnf(c_0_198, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0)),esk5_0)), inference(rw,[status(thm)],[c_0_191, c_0_190])).
% 0.60/0.81  cnf(c_0_199, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0)),esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_193]), c_0_194]), c_0_195]), c_0_196])]), c_0_197])).
% 0.60/0.81  cnf(c_0_200, negated_conjecture, (~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_182, c_0_190])).
% 0.60/0.81  cnf(c_0_201, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_198, c_0_199])])).
% 0.60/0.81  cnf(c_0_202, negated_conjecture, (v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,X1,esk5_0)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_171]), c_0_101]), c_0_101]), c_0_76]), c_0_77]), c_0_101]), c_0_101]), c_0_111])])).
% 0.60/0.81  cnf(c_0_203, negated_conjecture, (~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_200, c_0_201])])).
% 0.60/0.81  cnf(c_0_204, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202, c_0_199]), c_0_194]), c_0_195]), c_0_196])]), c_0_203]), ['proof']).
% 0.60/0.81  # SZS output end CNFRefutation
% 0.60/0.81  # Proof object total steps             : 205
% 0.60/0.81  # Proof object clause steps            : 165
% 0.60/0.81  # Proof object formula steps           : 40
% 0.60/0.81  # Proof object conjectures             : 115
% 0.60/0.81  # Proof object clause conjectures      : 112
% 0.60/0.81  # Proof object formula conjectures     : 3
% 0.60/0.81  # Proof object initial clauses used    : 37
% 0.60/0.81  # Proof object initial formulas used   : 20
% 0.60/0.81  # Proof object generating inferences   : 97
% 0.60/0.81  # Proof object simplifying inferences  : 300
% 0.60/0.81  # Training examples: 0 positive, 0 negative
% 0.60/0.81  # Parsed axioms                        : 21
% 0.60/0.81  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.81  # Initial clauses                      : 53
% 0.60/0.81  # Removed in clause preprocessing      : 1
% 0.60/0.81  # Initial clauses in saturation        : 52
% 0.60/0.81  # Processed clauses                    : 2650
% 0.60/0.81  # ...of these trivial                  : 11
% 0.60/0.81  # ...subsumed                          : 1256
% 0.60/0.81  # ...remaining for further processing  : 1382
% 0.60/0.81  # Other redundant clauses eliminated   : 9
% 0.60/0.81  # Clauses deleted for lack of memory   : 0
% 0.60/0.81  # Backward-subsumed                    : 346
% 0.60/0.81  # Backward-rewritten                   : 502
% 0.60/0.81  # Generated clauses                    : 4697
% 0.60/0.81  # ...of the previous two non-trivial   : 3796
% 0.60/0.81  # Contextual simplify-reflections      : 40
% 0.60/0.81  # Paramodulations                      : 4688
% 0.60/0.81  # Factorizations                       : 0
% 0.60/0.81  # Equation resolutions                 : 9
% 0.60/0.81  # Propositional unsat checks           : 0
% 0.60/0.81  #    Propositional check models        : 0
% 0.60/0.81  #    Propositional check unsatisfiable : 0
% 0.60/0.81  #    Propositional clauses             : 0
% 0.60/0.81  #    Propositional clauses after purity: 0
% 0.60/0.81  #    Propositional unsat core size     : 0
% 0.60/0.81  #    Propositional preprocessing time  : 0.000
% 0.60/0.81  #    Propositional encoding time       : 0.000
% 0.60/0.81  #    Propositional solver time         : 0.000
% 0.60/0.81  #    Success case prop preproc time    : 0.000
% 0.60/0.81  #    Success case prop encoding time   : 0.000
% 0.60/0.81  #    Success case prop solver time     : 0.000
% 0.60/0.81  # Current number of processed clauses  : 475
% 0.60/0.81  #    Positive orientable unit clauses  : 53
% 0.60/0.81  #    Positive unorientable unit clauses: 0
% 0.60/0.81  #    Negative unit clauses             : 2
% 0.60/0.81  #    Non-unit-clauses                  : 420
% 0.60/0.81  # Current number of unprocessed clauses: 695
% 0.60/0.81  # ...number of literals in the above   : 5511
% 0.60/0.81  # Current number of archived formulas  : 0
% 0.60/0.81  # Current number of archived clauses   : 898
% 0.60/0.81  # Clause-clause subsumption calls (NU) : 644305
% 0.60/0.81  # Rec. Clause-clause subsumption calls : 53384
% 0.60/0.81  # Non-unit clause-clause subsumptions  : 1481
% 0.60/0.81  # Unit Clause-clause subsumption calls : 1743
% 0.60/0.81  # Rewrite failures with RHS unbound    : 0
% 0.60/0.81  # BW rewrite match attempts            : 69
% 0.60/0.81  # BW rewrite match successes           : 17
% 0.60/0.81  # Condensation attempts                : 0
% 0.60/0.81  # Condensation successes               : 0
% 0.60/0.81  # Termbank termtop insertions          : 154958
% 0.60/0.81  
% 0.60/0.81  # -------------------------------------------------
% 0.60/0.81  # User time                : 0.460 s
% 0.60/0.81  # System time              : 0.012 s
% 0.60/0.81  # Total time               : 0.472 s
% 0.60/0.81  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
