%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:22 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  144 (11641 expanded)
%              Number of clauses        :  105 (4528 expanded)
%              Number of leaves         :   19 (2726 expanded)
%              Depth                    :   31
%              Number of atoms          :  608 (88707 expanded)
%              Number of equality atoms :   65 (6765 expanded)
%              Maximal formula depth    :   19 (   5 average)
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

fof(t13_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( r1_tarski(k1_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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

fof(c_0_19,negated_conjecture,(
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

fof(c_0_20,plain,(
    ! [X78,X79,X80,X81] :
      ( ( ~ v5_pre_topc(X80,X78,X79)
        | v5_pre_topc(X81,g1_pre_topc(u1_struct_0(X78),u1_pre_topc(X78)),X79)
        | X80 != X81
        | ~ v1_funct_1(X81)
        | ~ v1_funct_2(X81,u1_struct_0(g1_pre_topc(u1_struct_0(X78),u1_pre_topc(X78))),u1_struct_0(X79))
        | ~ m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X78),u1_pre_topc(X78))),u1_struct_0(X79))))
        | ~ v1_funct_1(X80)
        | ~ v1_funct_2(X80,u1_struct_0(X78),u1_struct_0(X79))
        | ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X78),u1_struct_0(X79))))
        | ~ v2_pre_topc(X79)
        | ~ l1_pre_topc(X79)
        | ~ v2_pre_topc(X78)
        | ~ l1_pre_topc(X78) )
      & ( ~ v5_pre_topc(X81,g1_pre_topc(u1_struct_0(X78),u1_pre_topc(X78)),X79)
        | v5_pre_topc(X80,X78,X79)
        | X80 != X81
        | ~ v1_funct_1(X81)
        | ~ v1_funct_2(X81,u1_struct_0(g1_pre_topc(u1_struct_0(X78),u1_pre_topc(X78))),u1_struct_0(X79))
        | ~ m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X78),u1_pre_topc(X78))),u1_struct_0(X79))))
        | ~ v1_funct_1(X80)
        | ~ v1_funct_2(X80,u1_struct_0(X78),u1_struct_0(X79))
        | ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X78),u1_struct_0(X79))))
        | ~ v2_pre_topc(X79)
        | ~ l1_pre_topc(X79)
        | ~ v2_pre_topc(X78)
        | ~ l1_pre_topc(X78) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).

fof(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & v2_pre_topc(esk7_0)
    & l1_pre_topc(esk7_0)
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))))
    & v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))
    & esk8_0 = esk9_0
    & ( ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
      | ~ v5_pre_topc(esk9_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) )
    & ( v5_pre_topc(esk8_0,esk6_0,esk7_0)
      | v5_pre_topc(esk9_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_22,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( esk8_0 = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk9_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X44,X45,X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X46)))
      | ~ r1_tarski(k1_relat_1(X47),X45)
      | m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).

fof(c_0_27,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | v1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_28,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ v5_pre_topc(esk9_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k1_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,plain,(
    ! [X29,X30] :
      ( ( ~ v4_relat_1(X30,X29)
        | r1_tarski(k1_relat_1(X30),X29)
        | ~ v1_relat_1(X30) )
      & ( ~ r1_tarski(k1_relat_1(X30),X29)
        | v4_relat_1(X30,X29)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_37,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_38,plain,(
    ! [X35,X36,X37] :
      ( ( v4_relat_1(X37,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( v5_relat_1(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_39,plain,(
    ! [X82,X83,X84,X85] :
      ( ( ~ v5_pre_topc(X84,X82,X83)
        | v5_pre_topc(X85,X82,g1_pre_topc(u1_struct_0(X83),u1_pre_topc(X83)))
        | X84 != X85
        | ~ v1_funct_1(X85)
        | ~ v1_funct_2(X85,u1_struct_0(X82),u1_struct_0(g1_pre_topc(u1_struct_0(X83),u1_pre_topc(X83))))
        | ~ m1_subset_1(X85,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X82),u1_struct_0(g1_pre_topc(u1_struct_0(X83),u1_pre_topc(X83))))))
        | ~ v1_funct_1(X84)
        | ~ v1_funct_2(X84,u1_struct_0(X82),u1_struct_0(X83))
        | ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X82),u1_struct_0(X83))))
        | ~ v2_pre_topc(X83)
        | ~ l1_pre_topc(X83)
        | ~ v2_pre_topc(X82)
        | ~ l1_pre_topc(X82) )
      & ( ~ v5_pre_topc(X85,X82,g1_pre_topc(u1_struct_0(X83),u1_pre_topc(X83)))
        | v5_pre_topc(X84,X82,X83)
        | X84 != X85
        | ~ v1_funct_1(X85)
        | ~ v1_funct_2(X85,u1_struct_0(X82),u1_struct_0(g1_pre_topc(u1_struct_0(X83),u1_pre_topc(X83))))
        | ~ m1_subset_1(X85,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X82),u1_struct_0(g1_pre_topc(u1_struct_0(X83),u1_pre_topc(X83))))))
        | ~ v1_funct_1(X84)
        | ~ v1_funct_2(X84,u1_struct_0(X82),u1_struct_0(X83))
        | ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X82),u1_struct_0(X83))))
        | ~ v2_pre_topc(X83)
        | ~ l1_pre_topc(X83)
        | ~ v2_pre_topc(X82)
        | ~ l1_pre_topc(X82) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v5_pre_topc(esk8_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))
    | ~ r1_tarski(k1_relat_1(esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_30])).

cnf(c_0_46,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_47,plain,(
    ! [X56,X57,X58] :
      ( ( v1_funct_1(X58)
        | ~ v1_funct_1(X58)
        | ~ v1_partfun1(X58,X56)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( v1_funct_2(X58,X56,X57)
        | ~ v1_funct_1(X58)
        | ~ v1_partfun1(X58,X56)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_48,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk7_0))))
    | ~ r1_tarski(k1_relat_1(esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))
    | ~ v4_relat_1(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_52,negated_conjecture,
    ( v4_relat_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_40])).

cnf(c_0_53,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk7_0))))
    | ~ v4_relat_1(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_44]),c_0_45])])).

cnf(c_0_58,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_2(esk8_0,X1,u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))
    | ~ v1_partfun1(esk8_0,X1)
    | ~ v4_relat_1(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_51]),c_0_34])])).

cnf(c_0_60,negated_conjecture,
    ( v5_pre_topc(esk8_0,X1,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v5_pre_topc(esk8_0,X1,esk7_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(esk8_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))
    | ~ v1_funct_2(esk8_0,u1_struct_0(X1),u1_struct_0(esk7_0))
    | ~ v4_relat_1(esk8_0,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_51]),c_0_55]),c_0_56]),c_0_34])]),c_0_57])).

fof(c_0_61,plain,(
    ! [X64,X65,X66] :
      ( ( X65 = k1_xboole_0
        | v1_partfun1(X66,X64)
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,X64,X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))
        | ~ v1_funct_1(X66)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( X64 != k1_xboole_0
        | v1_partfun1(X66,X64)
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,X64,X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))
        | ~ v1_funct_1(X66)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

cnf(c_0_62,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v1_partfun1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_52])])).

cnf(c_0_63,negated_conjecture,
    ( v5_pre_topc(esk8_0,X1,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v5_pre_topc(esk8_0,X1,esk7_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(esk8_0,u1_struct_0(X1),u1_struct_0(esk7_0))
    | ~ v1_partfun1(esk8_0,u1_struct_0(X1))
    | ~ v4_relat_1(esk8_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_65,plain,(
    ! [X77] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X77),u1_pre_topc(X77)))
        | ~ v2_pre_topc(X77)
        | ~ l1_pre_topc(X77) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X77),u1_pre_topc(X77)))
        | ~ v2_pre_topc(X77)
        | ~ l1_pre_topc(X77) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

fof(c_0_66,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v1_partfun1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_31]),c_0_32]),c_0_64]),c_0_52])])).

cnf(c_0_69,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_70,plain,(
    ! [X74,X75] :
      ( ( v1_pre_topc(g1_pre_topc(X74,X75))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k1_zfmisc_1(X74))) )
      & ( l1_pre_topc(g1_pre_topc(X74,X75))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k1_zfmisc_1(X74))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_73,plain,(
    ! [X59,X60] :
      ( ( ~ v1_partfun1(X60,X59)
        | k1_relat_1(X60) = X59
        | ~ v1_relat_1(X60)
        | ~ v4_relat_1(X60,X59) )
      & ( k1_relat_1(X60) != X59
        | v1_partfun1(X60,X59)
        | ~ v1_relat_1(X60)
        | ~ v4_relat_1(X60,X59) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v1_partfun1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_55]),c_0_56])])).

cnf(c_0_76,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_79,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | v1_partfun1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_40]),c_0_64]),c_0_34])])).

cnf(c_0_81,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ v1_partfun1(esk8_0,u1_struct_0(esk6_0))
    | ~ m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,plain,
    ( v1_partfun1(X1,X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

fof(c_0_83,plain,(
    ! [X76] :
      ( ~ l1_pre_topc(X76)
      | m1_subset_1(u1_pre_topc(X76),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X76)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_84,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | v5_pre_topc(esk9_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_86,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk8_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( k1_relat_1(esk8_0) = u1_struct_0(esk6_0)
    | u1_struct_0(esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_52]),c_0_45])])).

cnf(c_0_89,negated_conjecture,
    ( k1_relat_1(esk8_0) != u1_struct_0(esk6_0)
    | ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_52]),c_0_45])])).

cnf(c_0_90,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_92,negated_conjecture,
    ( v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | v5_pre_topc(esk8_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_85,c_0_24])).

cnf(c_0_93,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( k1_relat_1(esk8_0) != u1_struct_0(esk6_0)
    | ~ v5_pre_topc(esk8_0,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_55])])).

cnf(c_0_96,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( v5_pre_topc(esk8_0,X1,esk7_0)
    | ~ v5_pre_topc(esk8_0,X1,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(esk8_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))
    | ~ v1_funct_2(esk8_0,u1_struct_0(X1),u1_struct_0(esk7_0))
    | ~ v4_relat_1(esk8_0,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_51]),c_0_55]),c_0_56]),c_0_34])]),c_0_57])).

cnf(c_0_98,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_94]),c_0_34])]),c_0_80])).

cnf(c_0_99,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | ~ v5_pre_topc(esk8_0,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_88])).

cnf(c_0_100,negated_conjecture,
    ( v4_relat_1(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_30])).

fof(c_0_101,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_102,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_103,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_51]),c_0_52])])).

cnf(c_0_104,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | ~ v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_31]),c_0_32]),c_0_64]),c_0_52])]),c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_100])).

cnf(c_0_106,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

fof(c_0_108,plain,(
    ! [X18,X19] :
      ( ( k2_zfmisc_1(X18,X19) != k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_109,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_98]),c_0_99]),c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),esk7_0)
    | ~ v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_30]),c_0_55]),c_0_56]),c_0_33]),c_0_34])]),c_0_105])])).

cnf(c_0_111,negated_conjecture,
    ( v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),esk7_0)
    | ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_105]),c_0_55]),c_0_31]),c_0_56]),c_0_32]),c_0_64]),c_0_34]),c_0_40])])).

cnf(c_0_112,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_113,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

fof(c_0_114,plain,(
    ! [X20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_115,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_69]),c_0_55]),c_0_56])])).

fof(c_0_116,plain,(
    ! [X61,X62] :
      ( m1_subset_1(esk4_2(X61,X62),k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
      & v1_relat_1(esk4_2(X61,X62))
      & v4_relat_1(esk4_2(X61,X62),X61)
      & v5_relat_1(esk4_2(X61,X62),X62)
      & v1_funct_1(esk4_2(X61,X62))
      & v1_funct_2(esk4_2(X61,X62),X61,X62) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).

cnf(c_0_117,negated_conjecture,
    ( v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),esk7_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_92]),c_0_111])).

cnf(c_0_118,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_107])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(esk7_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_113])).

cnf(c_0_120,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_121,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | ~ m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_115,c_0_76])).

cnf(c_0_122,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_123,negated_conjecture,
    ( v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_30]),c_0_55]),c_0_56]),c_0_33]),c_0_34])]),c_0_105])]),c_0_117])).

cnf(c_0_124,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | u1_struct_0(esk7_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_120])])).

cnf(c_0_125,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_90]),c_0_55])])).

cnf(c_0_126,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(k1_xboole_0))
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_122,c_0_113])).

cnf(c_0_127,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_123])).

cnf(c_0_128,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_125])])).

cnf(c_0_129,plain,
    ( v1_funct_2(esk4_2(X1,X2),X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_130,plain,
    ( esk4_2(X1,X2) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_126]),c_0_120])])).

cnf(c_0_131,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk6_0,esk7_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_125]),c_0_128]),c_0_128])).

cnf(c_0_132,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_133,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk6_0,esk7_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_134,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk6_0,esk7_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_69]),c_0_31]),c_0_32])])).

cnf(c_0_135,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk6_0,esk7_0)
    | ~ m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_134,c_0_76])).

cnf(c_0_136,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),esk7_0)
    | ~ v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_105]),c_0_55]),c_0_31]),c_0_56]),c_0_32]),c_0_64]),c_0_34]),c_0_40])])).

cnf(c_0_137,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_90]),c_0_31])])).

cnf(c_0_138,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),esk7_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_136,c_0_125]),c_0_128]),c_0_128]),c_0_128]),c_0_137])).

cnf(c_0_139,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_125]),c_0_128]),c_0_128]),c_0_138])).

cnf(c_0_140,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_139,c_0_132])).

cnf(c_0_141,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_69]),c_0_31]),c_0_32])])).

cnf(c_0_142,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_141,c_0_76])).

cnf(c_0_143,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_90]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.48/0.68  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_URBAN_S0Y
% 0.48/0.68  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.48/0.68  #
% 0.48/0.68  # Preprocessing time       : 0.045 s
% 0.48/0.68  
% 0.48/0.68  # Proof found!
% 0.48/0.68  # SZS status Theorem
% 0.48/0.68  # SZS output start CNFRefutation
% 0.48/0.68  fof(t64_pre_topc, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_pre_topc)).
% 0.48/0.68  fof(t62_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 0.48/0.68  fof(t13_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 0.48/0.68  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.48/0.68  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.48/0.68  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.48/0.68  fof(t63_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_pre_topc)).
% 0.48/0.68  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.48/0.68  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 0.48/0.68  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.48/0.68  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.48/0.68  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.48/0.68  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.48/0.68  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.48/0.68  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.48/0.68  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.48/0.68  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.48/0.68  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.48/0.68  fof(rc1_funct_2, axiom, ![X1, X2]:?[X3]:(((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&v1_relat_1(X3))&v4_relat_1(X3,X1))&v5_relat_1(X3,X2))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 0.48/0.68  fof(c_0_19, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))))), inference(assume_negation,[status(cth)],[t64_pre_topc])).
% 0.48/0.68  fof(c_0_20, plain, ![X78, X79, X80, X81]:((~v5_pre_topc(X80,X78,X79)|v5_pre_topc(X81,g1_pre_topc(u1_struct_0(X78),u1_pre_topc(X78)),X79)|X80!=X81|(~v1_funct_1(X81)|~v1_funct_2(X81,u1_struct_0(g1_pre_topc(u1_struct_0(X78),u1_pre_topc(X78))),u1_struct_0(X79))|~m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X78),u1_pre_topc(X78))),u1_struct_0(X79)))))|(~v1_funct_1(X80)|~v1_funct_2(X80,u1_struct_0(X78),u1_struct_0(X79))|~m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X78),u1_struct_0(X79)))))|(~v2_pre_topc(X79)|~l1_pre_topc(X79))|(~v2_pre_topc(X78)|~l1_pre_topc(X78)))&(~v5_pre_topc(X81,g1_pre_topc(u1_struct_0(X78),u1_pre_topc(X78)),X79)|v5_pre_topc(X80,X78,X79)|X80!=X81|(~v1_funct_1(X81)|~v1_funct_2(X81,u1_struct_0(g1_pre_topc(u1_struct_0(X78),u1_pre_topc(X78))),u1_struct_0(X79))|~m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X78),u1_pre_topc(X78))),u1_struct_0(X79)))))|(~v1_funct_1(X80)|~v1_funct_2(X80,u1_struct_0(X78),u1_struct_0(X79))|~m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X78),u1_struct_0(X79)))))|(~v2_pre_topc(X79)|~l1_pre_topc(X79))|(~v2_pre_topc(X78)|~l1_pre_topc(X78)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).
% 0.48/0.68  fof(c_0_21, negated_conjecture, ((v2_pre_topc(esk6_0)&l1_pre_topc(esk6_0))&((v2_pre_topc(esk7_0)&l1_pre_topc(esk7_0))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)))))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))))&(esk8_0=esk9_0&((~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~v5_pre_topc(esk9_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))&(v5_pre_topc(esk8_0,esk6_0,esk7_0)|v5_pre_topc(esk9_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.48/0.68  cnf(c_0_22, plain, (v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.48/0.68  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.68  cnf(c_0_24, negated_conjecture, (esk8_0=esk9_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.68  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk9_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.68  fof(c_0_26, plain, ![X44, X45, X46, X47]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X46)))|(~r1_tarski(k1_relat_1(X47),X45)|m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).
% 0.48/0.68  fof(c_0_27, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|v1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.48/0.68  cnf(c_0_28, negated_conjecture, (~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~v5_pre_topc(esk9_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.68  cnf(c_0_29, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_22])).
% 0.48/0.68  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.48/0.68  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.68  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.68  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 0.48/0.68  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.68  cnf(c_0_35, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k1_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.48/0.68  fof(c_0_36, plain, ![X29, X30]:((~v4_relat_1(X30,X29)|r1_tarski(k1_relat_1(X30),X29)|~v1_relat_1(X30))&(~r1_tarski(k1_relat_1(X30),X29)|v4_relat_1(X30,X29)|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.48/0.68  cnf(c_0_37, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.48/0.68  fof(c_0_38, plain, ![X35, X36, X37]:((v4_relat_1(X37,X35)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(v5_relat_1(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.48/0.68  fof(c_0_39, plain, ![X82, X83, X84, X85]:((~v5_pre_topc(X84,X82,X83)|v5_pre_topc(X85,X82,g1_pre_topc(u1_struct_0(X83),u1_pre_topc(X83)))|X84!=X85|(~v1_funct_1(X85)|~v1_funct_2(X85,u1_struct_0(X82),u1_struct_0(g1_pre_topc(u1_struct_0(X83),u1_pre_topc(X83))))|~m1_subset_1(X85,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X82),u1_struct_0(g1_pre_topc(u1_struct_0(X83),u1_pre_topc(X83)))))))|(~v1_funct_1(X84)|~v1_funct_2(X84,u1_struct_0(X82),u1_struct_0(X83))|~m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X82),u1_struct_0(X83)))))|(~v2_pre_topc(X83)|~l1_pre_topc(X83))|(~v2_pre_topc(X82)|~l1_pre_topc(X82)))&(~v5_pre_topc(X85,X82,g1_pre_topc(u1_struct_0(X83),u1_pre_topc(X83)))|v5_pre_topc(X84,X82,X83)|X84!=X85|(~v1_funct_1(X85)|~v1_funct_2(X85,u1_struct_0(X82),u1_struct_0(g1_pre_topc(u1_struct_0(X83),u1_pre_topc(X83))))|~m1_subset_1(X85,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X82),u1_struct_0(g1_pre_topc(u1_struct_0(X83),u1_pre_topc(X83)))))))|(~v1_funct_1(X84)|~v1_funct_2(X84,u1_struct_0(X82),u1_struct_0(X83))|~m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X82),u1_struct_0(X83)))))|(~v2_pre_topc(X83)|~l1_pre_topc(X83))|(~v2_pre_topc(X82)|~l1_pre_topc(X82)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).
% 0.48/0.68  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.68  cnf(c_0_41, negated_conjecture, (~v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v5_pre_topc(esk8_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_28, c_0_24])).
% 0.48/0.68  cnf(c_0_42, negated_conjecture, (v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])])).
% 0.48/0.68  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))|~r1_tarski(k1_relat_1(esk8_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_30])).
% 0.48/0.68  cnf(c_0_44, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.48/0.68  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_37, c_0_30])).
% 0.48/0.68  cnf(c_0_46, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.48/0.68  fof(c_0_47, plain, ![X56, X57, X58]:((v1_funct_1(X58)|(~v1_funct_1(X58)|~v1_partfun1(X58,X56))|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))&(v1_funct_2(X58,X56,X57)|(~v1_funct_1(X58)|~v1_partfun1(X58,X56))|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.48/0.68  cnf(c_0_48, plain, (v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.48/0.68  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk7_0))))|~r1_tarski(k1_relat_1(esk8_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_40])).
% 0.48/0.68  cnf(c_0_50, negated_conjecture, (~v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.48/0.68  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))|~v4_relat_1(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.48/0.68  cnf(c_0_52, negated_conjecture, (v4_relat_1(esk8_0,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_46, c_0_40])).
% 0.48/0.68  cnf(c_0_53, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.48/0.68  cnf(c_0_54, plain, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_48])).
% 0.48/0.68  cnf(c_0_55, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.68  cnf(c_0_56, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.68  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk7_0))))|~v4_relat_1(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_44]), c_0_45])])).
% 0.48/0.68  cnf(c_0_58, negated_conjecture, (~v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.48/0.68  cnf(c_0_59, negated_conjecture, (v1_funct_2(esk8_0,X1,u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))|~v1_partfun1(esk8_0,X1)|~v4_relat_1(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_51]), c_0_34])])).
% 0.48/0.68  cnf(c_0_60, negated_conjecture, (v5_pre_topc(esk8_0,X1,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v5_pre_topc(esk8_0,X1,esk7_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(esk8_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))|~v1_funct_2(esk8_0,u1_struct_0(X1),u1_struct_0(esk7_0))|~v4_relat_1(esk8_0,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_51]), c_0_55]), c_0_56]), c_0_34])]), c_0_57])).
% 0.48/0.68  fof(c_0_61, plain, ![X64, X65, X66]:((X65=k1_xboole_0|v1_partfun1(X66,X64)|(~v1_funct_1(X66)|~v1_funct_2(X66,X64,X65)|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))))|(~v1_funct_1(X66)|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))))&(X64!=k1_xboole_0|v1_partfun1(X66,X64)|(~v1_funct_1(X66)|~v1_funct_2(X66,X64,X65)|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))))|(~v1_funct_1(X66)|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.48/0.68  cnf(c_0_62, negated_conjecture, (~v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v1_partfun1(esk8_0,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_52])])).
% 0.48/0.68  cnf(c_0_63, negated_conjecture, (v5_pre_topc(esk8_0,X1,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v5_pre_topc(esk8_0,X1,esk7_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(esk8_0,u1_struct_0(X1),u1_struct_0(esk7_0))|~v1_partfun1(esk8_0,u1_struct_0(X1))|~v4_relat_1(esk8_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_60, c_0_59])).
% 0.48/0.68  cnf(c_0_64, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.68  fof(c_0_65, plain, ![X77]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X77),u1_pre_topc(X77)))|(~v2_pre_topc(X77)|~l1_pre_topc(X77)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X77),u1_pre_topc(X77)))|(~v2_pre_topc(X77)|~l1_pre_topc(X77)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.48/0.68  fof(c_0_66, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.48/0.68  cnf(c_0_67, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.48/0.68  cnf(c_0_68, negated_conjecture, (~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v1_partfun1(esk8_0,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_31]), c_0_32]), c_0_64]), c_0_52])])).
% 0.48/0.68  cnf(c_0_69, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.48/0.68  fof(c_0_70, plain, ![X74, X75]:((v1_pre_topc(g1_pre_topc(X74,X75))|~m1_subset_1(X75,k1_zfmisc_1(k1_zfmisc_1(X74))))&(l1_pre_topc(g1_pre_topc(X74,X75))|~m1_subset_1(X75,k1_zfmisc_1(k1_zfmisc_1(X74))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.48/0.68  cnf(c_0_71, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.48/0.68  cnf(c_0_72, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.48/0.68  fof(c_0_73, plain, ![X59, X60]:((~v1_partfun1(X60,X59)|k1_relat_1(X60)=X59|(~v1_relat_1(X60)|~v4_relat_1(X60,X59)))&(k1_relat_1(X60)!=X59|v1_partfun1(X60,X59)|(~v1_relat_1(X60)|~v4_relat_1(X60,X59)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.48/0.68  cnf(c_0_74, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_67])).
% 0.48/0.68  cnf(c_0_75, negated_conjecture, (~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v1_partfun1(esk8_0,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_55]), c_0_56])])).
% 0.48/0.68  cnf(c_0_76, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.48/0.68  cnf(c_0_77, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.48/0.68  cnf(c_0_78, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.48/0.68  cnf(c_0_79, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.48/0.68  cnf(c_0_80, negated_conjecture, (u1_struct_0(esk7_0)=k1_xboole_0|v1_partfun1(esk8_0,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_40]), c_0_64]), c_0_34])])).
% 0.48/0.68  cnf(c_0_81, negated_conjecture, (~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~v1_partfun1(esk8_0,u1_struct_0(esk6_0))|~m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.48/0.68  cnf(c_0_82, plain, (v1_partfun1(X1,X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.48/0.68  fof(c_0_83, plain, ![X76]:(~l1_pre_topc(X76)|m1_subset_1(u1_pre_topc(X76),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X76))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.48/0.68  cnf(c_0_84, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_77])).
% 0.48/0.68  cnf(c_0_85, negated_conjecture, (v5_pre_topc(esk8_0,esk6_0,esk7_0)|v5_pre_topc(esk9_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.68  cnf(c_0_86, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.48/0.68  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk8_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))), inference(spm,[status(thm)],[c_0_43, c_0_78])).
% 0.48/0.68  cnf(c_0_88, negated_conjecture, (k1_relat_1(esk8_0)=u1_struct_0(esk6_0)|u1_struct_0(esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_52]), c_0_45])])).
% 0.48/0.68  cnf(c_0_89, negated_conjecture, (k1_relat_1(esk8_0)!=u1_struct_0(esk6_0)|~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_52]), c_0_45])])).
% 0.48/0.68  cnf(c_0_90, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.48/0.68  cnf(c_0_91, negated_conjecture, (v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])])).
% 0.48/0.68  cnf(c_0_92, negated_conjecture, (v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|v5_pre_topc(esk8_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_85, c_0_24])).
% 0.48/0.68  cnf(c_0_93, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_86])).
% 0.48/0.68  cnf(c_0_94, negated_conjecture, (u1_struct_0(esk7_0)=k1_xboole_0|m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.48/0.68  cnf(c_0_95, negated_conjecture, (k1_relat_1(esk8_0)!=u1_struct_0(esk6_0)|~v5_pre_topc(esk8_0,esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_55])])).
% 0.48/0.68  cnf(c_0_96, negated_conjecture, (v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|v5_pre_topc(esk8_0,esk6_0,esk7_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.48/0.68  cnf(c_0_97, negated_conjecture, (v5_pre_topc(esk8_0,X1,esk7_0)|~v5_pre_topc(esk8_0,X1,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(esk8_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))|~v1_funct_2(esk8_0,u1_struct_0(X1),u1_struct_0(esk7_0))|~v4_relat_1(esk8_0,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_51]), c_0_55]), c_0_56]), c_0_34])]), c_0_57])).
% 0.48/0.68  cnf(c_0_98, negated_conjecture, (u1_struct_0(esk7_0)=k1_xboole_0|v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_94]), c_0_34])]), c_0_80])).
% 0.48/0.68  cnf(c_0_99, negated_conjecture, (u1_struct_0(esk7_0)=k1_xboole_0|~v5_pre_topc(esk8_0,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_95, c_0_88])).
% 0.48/0.68  cnf(c_0_100, negated_conjecture, (v4_relat_1(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))))), inference(spm,[status(thm)],[c_0_46, c_0_30])).
% 0.48/0.68  fof(c_0_101, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.48/0.68  fof(c_0_102, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.48/0.68  cnf(c_0_103, negated_conjecture, (v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|v5_pre_topc(esk8_0,esk6_0,esk7_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_51]), c_0_52])])).
% 0.48/0.68  cnf(c_0_104, negated_conjecture, (u1_struct_0(esk7_0)=k1_xboole_0|~v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_31]), c_0_32]), c_0_64]), c_0_52])]), c_0_99])).
% 0.48/0.68  cnf(c_0_105, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))))), inference(spm,[status(thm)],[c_0_57, c_0_100])).
% 0.48/0.68  cnf(c_0_106, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.48/0.68  cnf(c_0_107, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.48/0.68  fof(c_0_108, plain, ![X18, X19]:((k2_zfmisc_1(X18,X19)!=k1_xboole_0|(X18=k1_xboole_0|X19=k1_xboole_0))&((X18!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0)&(X19!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.48/0.68  cnf(c_0_109, negated_conjecture, (u1_struct_0(esk7_0)=k1_xboole_0|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_98]), c_0_99]), c_0_104])).
% 0.48/0.68  cnf(c_0_110, negated_conjecture, (v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),esk7_0)|~v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_30]), c_0_55]), c_0_56]), c_0_33]), c_0_34])]), c_0_105])])).
% 0.48/0.68  cnf(c_0_111, negated_conjecture, (v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),esk7_0)|~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_105]), c_0_55]), c_0_31]), c_0_56]), c_0_32]), c_0_64]), c_0_34]), c_0_40])])).
% 0.48/0.68  cnf(c_0_112, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.48/0.68  cnf(c_0_113, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_108])).
% 0.48/0.68  fof(c_0_114, plain, ![X20]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.48/0.68  cnf(c_0_115, negated_conjecture, (u1_struct_0(esk7_0)=k1_xboole_0|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_69]), c_0_55]), c_0_56])])).
% 0.48/0.68  fof(c_0_116, plain, ![X61, X62]:(((((m1_subset_1(esk4_2(X61,X62),k1_zfmisc_1(k2_zfmisc_1(X61,X62)))&v1_relat_1(esk4_2(X61,X62)))&v4_relat_1(esk4_2(X61,X62),X61))&v5_relat_1(esk4_2(X61,X62),X62))&v1_funct_1(esk4_2(X61,X62)))&v1_funct_2(esk4_2(X61,X62),X61,X62)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).
% 0.48/0.68  cnf(c_0_117, negated_conjecture, (v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),esk7_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_92]), c_0_111])).
% 0.48/0.68  cnf(c_0_118, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_112, c_0_107])).
% 0.48/0.68  cnf(c_0_119, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0))|u1_struct_0(esk7_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_113])).
% 0.48/0.68  cnf(c_0_120, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_114])).
% 0.48/0.68  cnf(c_0_121, negated_conjecture, (u1_struct_0(esk7_0)=k1_xboole_0|~m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))), inference(spm,[status(thm)],[c_0_115, c_0_76])).
% 0.48/0.68  cnf(c_0_122, plain, (m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_116])).
% 0.48/0.68  cnf(c_0_123, negated_conjecture, (v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_30]), c_0_55]), c_0_56]), c_0_33]), c_0_34])]), c_0_105])]), c_0_117])).
% 0.48/0.68  cnf(c_0_124, negated_conjecture, (esk8_0=k1_xboole_0|u1_struct_0(esk7_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_120])])).
% 0.48/0.68  cnf(c_0_125, negated_conjecture, (u1_struct_0(esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_90]), c_0_55])])).
% 0.48/0.68  cnf(c_0_126, plain, (m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(k1_xboole_0))|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_122, c_0_113])).
% 0.48/0.68  cnf(c_0_127, negated_conjecture, (~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_41, c_0_123])).
% 0.48/0.68  cnf(c_0_128, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_125])])).
% 0.48/0.68  cnf(c_0_129, plain, (v1_funct_2(esk4_2(X1,X2),X1,X2)), inference(split_conjunct,[status(thm)],[c_0_116])).
% 0.48/0.68  cnf(c_0_130, plain, (esk4_2(X1,X2)=k1_xboole_0|X2!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_126]), c_0_120])])).
% 0.48/0.68  cnf(c_0_131, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk6_0,esk7_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_125]), c_0_128]), c_0_128])).
% 0.48/0.68  cnf(c_0_132, plain, (v1_funct_2(k1_xboole_0,X1,X2)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 0.48/0.68  cnf(c_0_133, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk6_0,esk7_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))), inference(spm,[status(thm)],[c_0_131, c_0_132])).
% 0.48/0.68  cnf(c_0_134, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk6_0,esk7_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_69]), c_0_31]), c_0_32])])).
% 0.48/0.68  cnf(c_0_135, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk6_0,esk7_0)|~m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(spm,[status(thm)],[c_0_134, c_0_76])).
% 0.48/0.68  cnf(c_0_136, negated_conjecture, (v5_pre_topc(esk8_0,esk6_0,esk7_0)|~v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),esk7_0)|~v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_105]), c_0_55]), c_0_31]), c_0_56]), c_0_32]), c_0_64]), c_0_34]), c_0_40])])).
% 0.48/0.68  cnf(c_0_137, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_90]), c_0_31])])).
% 0.48/0.68  cnf(c_0_138, negated_conjecture, (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),esk7_0)|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),k1_xboole_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_136, c_0_125]), c_0_128]), c_0_128]), c_0_128]), c_0_137])).
% 0.48/0.68  cnf(c_0_139, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_125]), c_0_128]), c_0_128]), c_0_138])).
% 0.48/0.68  cnf(c_0_140, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))), inference(spm,[status(thm)],[c_0_139, c_0_132])).
% 0.48/0.68  cnf(c_0_141, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_69]), c_0_31]), c_0_32])])).
% 0.48/0.68  cnf(c_0_142, negated_conjecture, (~m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(spm,[status(thm)],[c_0_141, c_0_76])).
% 0.48/0.68  cnf(c_0_143, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_90]), c_0_31])]), ['proof']).
% 0.48/0.68  # SZS output end CNFRefutation
% 0.48/0.68  # Proof object total steps             : 144
% 0.48/0.68  # Proof object clause steps            : 105
% 0.48/0.68  # Proof object formula steps           : 39
% 0.48/0.68  # Proof object conjectures             : 74
% 0.48/0.68  # Proof object clause conjectures      : 71
% 0.48/0.68  # Proof object formula conjectures     : 3
% 0.48/0.68  # Proof object initial clauses used    : 35
% 0.48/0.68  # Proof object initial formulas used   : 19
% 0.48/0.68  # Proof object generating inferences   : 57
% 0.48/0.68  # Proof object simplifying inferences  : 136
% 0.48/0.68  # Training examples: 0 positive, 0 negative
% 0.48/0.68  # Parsed axioms                        : 30
% 0.48/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.68  # Initial clauses                      : 70
% 0.48/0.68  # Removed in clause preprocessing      : 1
% 0.48/0.68  # Initial clauses in saturation        : 69
% 0.48/0.68  # Processed clauses                    : 1951
% 0.48/0.68  # ...of these trivial                  : 60
% 0.48/0.68  # ...subsumed                          : 881
% 0.48/0.68  # ...remaining for further processing  : 1010
% 0.48/0.68  # Other redundant clauses eliminated   : 14
% 0.48/0.68  # Clauses deleted for lack of memory   : 0
% 0.48/0.68  # Backward-subsumed                    : 94
% 0.48/0.68  # Backward-rewritten                   : 280
% 0.48/0.68  # Generated clauses                    : 8883
% 0.48/0.68  # ...of the previous two non-trivial   : 8004
% 0.48/0.68  # Contextual simplify-reflections      : 83
% 0.48/0.68  # Paramodulations                      : 8840
% 0.48/0.68  # Factorizations                       : 3
% 0.48/0.68  # Equation resolutions                 : 40
% 0.48/0.68  # Propositional unsat checks           : 0
% 0.48/0.68  #    Propositional check models        : 0
% 0.48/0.68  #    Propositional check unsatisfiable : 0
% 0.48/0.68  #    Propositional clauses             : 0
% 0.48/0.68  #    Propositional clauses after purity: 0
% 0.48/0.68  #    Propositional unsat core size     : 0
% 0.48/0.68  #    Propositional preprocessing time  : 0.000
% 0.48/0.68  #    Propositional encoding time       : 0.000
% 0.48/0.68  #    Propositional solver time         : 0.000
% 0.48/0.68  #    Success case prop preproc time    : 0.000
% 0.48/0.68  #    Success case prop encoding time   : 0.000
% 0.48/0.68  #    Success case prop solver time     : 0.000
% 0.48/0.68  # Current number of processed clauses  : 630
% 0.48/0.68  #    Positive orientable unit clauses  : 48
% 0.48/0.68  #    Positive unorientable unit clauses: 0
% 0.48/0.68  #    Negative unit clauses             : 4
% 0.48/0.68  #    Non-unit-clauses                  : 578
% 0.48/0.68  # Current number of unprocessed clauses: 4817
% 0.48/0.68  # ...number of literals in the above   : 28675
% 0.48/0.68  # Current number of archived formulas  : 0
% 0.48/0.68  # Current number of archived clauses   : 374
% 0.48/0.68  # Clause-clause subsumption calls (NU) : 223661
% 0.48/0.68  # Rec. Clause-clause subsumption calls : 43391
% 0.48/0.68  # Non-unit clause-clause subsumptions  : 979
% 0.48/0.68  # Unit Clause-clause subsumption calls : 6873
% 0.48/0.68  # Rewrite failures with RHS unbound    : 0
% 0.48/0.68  # BW rewrite match attempts            : 74
% 0.48/0.68  # BW rewrite match successes           : 15
% 0.48/0.68  # Condensation attempts                : 0
% 0.48/0.68  # Condensation successes               : 0
% 0.48/0.68  # Termbank termtop insertions          : 218551
% 0.48/0.68  
% 0.48/0.68  # -------------------------------------------------
% 0.48/0.68  # User time                : 0.330 s
% 0.48/0.68  # System time              : 0.007 s
% 0.48/0.68  # Total time               : 0.337 s
% 0.48/0.68  # Maximum resident set size: 1628 pages
%------------------------------------------------------------------------------
