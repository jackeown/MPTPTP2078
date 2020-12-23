%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:23 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  181 (108011 expanded)
%              Number of clauses        :  139 (40740 expanded)
%              Number of leaves         :   21 (25669 expanded)
%              Depth                    :   38
%              Number of atoms          :  749 (835522 expanded)
%              Number of equality atoms :   91 (68818 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(rc1_funct_2,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2)
      & v1_funct_1(X3)
      & v1_funct_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(cc6_funct_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & ~ v1_xboole_0(X3)
              & v1_funct_2(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

fof(c_0_21,negated_conjecture,(
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

fof(c_0_22,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_23,plain,(
    ! [X31,X32,X33] :
      ( ( v1_funct_1(X33)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | v1_xboole_0(X32) )
      & ( v1_partfun1(X33,X31)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | v1_xboole_0(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X25,X26,X27] :
      ( ( v4_relat_1(X27,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v5_relat_1(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_28,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | v1_relat_1(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_29,plain,(
    ! [X22,X23] : v1_relat_1(k2_zfmisc_1(X22,X23)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_30,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_xboole_0(X28)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X28)))
      | v1_xboole_0(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_31,plain,(
    ! [X37,X38] :
      ( ( ~ v1_partfun1(X38,X37)
        | k1_relat_1(X38) = X37
        | ~ v1_relat_1(X38)
        | ~ v4_relat_1(X38,X37) )
      & ( k1_relat_1(X38) != X37
        | v1_partfun1(X38,X37)
        | ~ v1_relat_1(X38)
        | ~ v4_relat_1(X38,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_32,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_39,plain,(
    ! [X50,X51,X52,X53] :
      ( ( ~ v5_pre_topc(X52,X50,X51)
        | v5_pre_topc(X53,X50,g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))
        | X52 != X53
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51))))
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51))))))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51))))
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50) )
      & ( ~ v5_pre_topc(X53,X50,g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))
        | v5_pre_topc(X52,X50,X51)
        | X52 != X53
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51))))
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51))))))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51))))
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( v1_partfun1(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_45,negated_conjecture,
    ( v4_relat_1(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_38])])).

cnf(c_0_47,plain,
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

cnf(c_0_48,negated_conjecture,
    ( v1_partfun1(esk6_0,u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_40]),c_0_41]),c_0_35])])).

cnf(c_0_49,negated_conjecture,
    ( v4_relat_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( k1_relat_1(esk6_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_53,plain,
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
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_56,plain,(
    ! [X15] :
      ( ~ v1_xboole_0(X15)
      | X15 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_57,negated_conjecture,
    ( k1_relat_1(esk6_0) = u1_struct_0(esk4_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_48]),c_0_49]),c_0_46])])).

cnf(c_0_58,negated_conjecture,
    ( k1_relat_1(esk6_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_40])).

fof(c_0_60,plain,(
    ! [X46,X47,X48,X49] :
      ( ( ~ v5_pre_topc(X48,X46,X47)
        | v5_pre_topc(X49,g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46)),X47)
        | X48 != X49
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X47))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X47))))
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( ~ v5_pre_topc(X49,g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46)),X47)
        | v5_pre_topc(X48,X46,X47)
        | X48 != X49
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X47))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X47))))
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).

cnf(c_0_61,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_52,c_0_25])).

cnf(c_0_62,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_33]),c_0_54]),c_0_55]),c_0_34]),c_0_35])])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | v1_xboole_0(esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_65,plain,
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

cnf(c_0_66,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,plain,
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
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_70,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_71,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_41]),c_0_40])])).

cnf(c_0_72,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | v5_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),X2)
    | ~ v5_pre_topc(X1,esk4_0,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_67]),c_0_69]),c_0_70])])).

fof(c_0_73,plain,(
    ! [X45] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)))
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)))
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

cnf(c_0_74,plain,
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

cnf(c_0_75,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_54]),c_0_55]),c_0_41]),c_0_35]),c_0_40])])).

cnf(c_0_76,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

fof(c_0_77,plain,(
    ! [X42,X43] :
      ( ( v1_pre_topc(g1_pre_topc(X42,X43))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k1_zfmisc_1(X42))) )
      & ( l1_pre_topc(g1_pre_topc(X42,X43))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k1_zfmisc_1(X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_78,plain,
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
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_80,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_69]),c_0_70])])).

cnf(c_0_81,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_82,plain,(
    ! [X44] :
      ( ~ l1_pre_topc(X44)
      | m1_subset_1(u1_pre_topc(X44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X44)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_83,plain,
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

cnf(c_0_84,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_33]),c_0_54]),c_0_55]),c_0_34]),c_0_35])])).

cnf(c_0_85,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_79,c_0_25])).

cnf(c_0_86,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_88,plain,
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
    inference(er,[status(thm)],[c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_70])])).

fof(c_0_91,plain,(
    ! [X16,X17] :
      ( ( k2_zfmisc_1(X16,X17) != k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_92,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | v5_pre_topc(X1,esk4_0,X2)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_67]),c_0_69]),c_0_70])])).

cnf(c_0_93,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_67]),c_0_41]),c_0_40])]),c_0_90])).

fof(c_0_94,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_95,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_96,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_54]),c_0_55]),c_0_41]),c_0_35]),c_0_40])]),c_0_90])).

fof(c_0_98,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_99,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_100,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_101,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_96]),c_0_63])).

cnf(c_0_102,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_103,plain,(
    ! [X39,X40] :
      ( m1_subset_1(esk3_2(X39,X40),k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      & v1_relat_1(esk3_2(X39,X40))
      & v4_relat_1(esk3_2(X39,X40),X39)
      & v5_relat_1(esk3_2(X39,X40),X40)
      & v1_funct_1(esk3_2(X39,X40))
      & v1_funct_2(esk3_2(X39,X40),X39,X40) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).

cnf(c_0_104,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_76]),c_0_69]),c_0_70])])).

cnf(c_0_105,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_106,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_107,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_108,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_109,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

fof(c_0_110,plain,(
    ! [X24] :
      ( ~ v1_xboole_0(X24)
      | v1_funct_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

cnf(c_0_111,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_33]),c_0_69]),c_0_70]),c_0_34]),c_0_35])])).

cnf(c_0_112,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_81])).

cnf(c_0_113,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_114,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_107])).

cnf(c_0_115,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(k1_xboole_0))
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_116,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_117,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_111])).

cnf(c_0_118,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_87]),c_0_70])])).

cnf(c_0_119,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_102])).

cnf(c_0_120,plain,
    ( v1_funct_2(esk3_2(X1,X2),X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_121,plain,
    ( esk3_2(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_122,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_107])).

cnf(c_0_123,plain,
    ( v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_107])).

cnf(c_0_124,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_118]),c_0_118]),c_0_118]),c_0_118]),c_0_119])])).

cnf(c_0_125,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_126,plain,
    ( v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | u1_struct_0(X2) != k1_xboole_0
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_109]),c_0_122]),c_0_123])).

cnf(c_0_127,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_128,plain,
    ( v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | u1_struct_0(X1) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_125]),c_0_119])]),c_0_125])).

cnf(c_0_129,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_54]),c_0_69]),c_0_55]),c_0_70])])).

fof(c_0_130,plain,(
    ! [X34,X35,X36] :
      ( ( v1_funct_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X34,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | v1_xboole_0(X34)
        | v1_xboole_0(X35) )
      & ( ~ v1_xboole_0(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X34,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | v1_xboole_0(X34)
        | v1_xboole_0(X35) )
      & ( v1_funct_2(X36,X34,X35)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X34,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | v1_xboole_0(X34)
        | v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).

cnf(c_0_131,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_33]),c_0_69]),c_0_70]),c_0_34]),c_0_35])])).

cnf(c_0_132,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_76]),c_0_54]),c_0_55])])).

cnf(c_0_133,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(k1_xboole_0))
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_108,c_0_96])).

cnf(c_0_134,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

cnf(c_0_135,plain,
    ( v1_funct_1(esk3_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_136,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(spm,[status(thm)],[c_0_131,c_0_85])).

cnf(c_0_137,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_132,c_0_81])).

cnf(c_0_138,plain,
    ( esk3_2(X1,X2) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_114,c_0_133])).

cnf(c_0_139,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_102])).

cnf(c_0_140,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[c_0_134,c_0_116])).

cnf(c_0_141,plain,
    ( v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),X1,X2)
    | ~ v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_108]),c_0_120]),c_0_135])])).

cnf(c_0_142,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_136,c_0_118]),c_0_118]),c_0_118]),c_0_118]),c_0_119])])).

cnf(c_0_143,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_87]),c_0_55])])).

cnf(c_0_144,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_118]),c_0_118]),c_0_118]),c_0_118]),c_0_119])])).

cnf(c_0_145,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_120,c_0_138])).

cnf(c_0_146,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v5_pre_topc(k1_xboole_0,X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_119]),c_0_139]),c_0_119])])).

cnf(c_0_147,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_40]),c_0_41])])).

cnf(c_0_148,plain,
    ( v5_pre_topc(k1_xboole_0,X1,X2)
    | u1_struct_0(X1) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_121]),c_0_119])]),c_0_125])).

cnf(c_0_149,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_125]),c_0_143])).

cnf(c_0_150,negated_conjecture,
    ( u1_struct_0(esk5_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_144,c_0_145])).

cnf(c_0_151,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | u1_struct_0(X2) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_145]),c_0_145])).

cnf(c_0_152,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_147])).

cnf(c_0_153,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_54]),c_0_69]),c_0_55]),c_0_70])]),c_0_143])).

cnf(c_0_154,negated_conjecture,
    ( u1_struct_0(esk5_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_151]),c_0_54]),c_0_69]),c_0_55]),c_0_70])])).

cnf(c_0_155,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | u1_struct_0(esk4_0) = k1_xboole_0
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_152])).

cnf(c_0_156,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_76]),c_0_54]),c_0_55])])).

cnf(c_0_157,plain,
    ( v1_xboole_0(esk3_2(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_108])).

cnf(c_0_158,negated_conjecture,
    ( u1_struct_0(esk5_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_76]),c_0_69]),c_0_70])])).

cnf(c_0_159,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | u1_struct_0(esk5_0) = k1_xboole_0
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_155,c_0_107])).

cnf(c_0_160,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_156,c_0_81])).

cnf(c_0_161,plain,
    ( esk3_2(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_157])).

cnf(c_0_162,negated_conjecture,
    ( u1_struct_0(esk5_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_158,c_0_81])).

cnf(c_0_163,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | u1_struct_0(esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_159,c_0_118]),c_0_119])])).

cnf(c_0_164,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_87]),c_0_55])])).

cnf(c_0_165,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_120,c_0_161])).

cnf(c_0_166,negated_conjecture,
    ( u1_struct_0(esk5_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_87]),c_0_70])])).

cnf(c_0_167,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_163,c_0_164])).

cnf(c_0_168,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_118]),c_0_118]),c_0_118]),c_0_118]),c_0_119])])).

cnf(c_0_169,plain,
    ( v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_165,c_0_102])).

cnf(c_0_170,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_118]),c_0_118])).

cnf(c_0_171,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_166,c_0_167])])).

cnf(c_0_172,plain,
    ( v5_pre_topc(X1,X2,X3)
    | u1_struct_0(X3) != k1_xboole_0
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_96]),c_0_122]),c_0_123])).

cnf(c_0_173,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_168,c_0_167]),c_0_167]),c_0_169])])).

cnf(c_0_174,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_170,c_0_167]),c_0_171])).

cnf(c_0_175,negated_conjecture,
    ( v5_pre_topc(X1,X2,esk5_0)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),esk5_0)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),k1_xboole_0)
    | ~ v1_funct_2(X1,u1_struct_0(X2),k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_167]),c_0_54]),c_0_55])])).

cnf(c_0_176,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_173,c_0_174])])).

cnf(c_0_177,negated_conjecture,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_176]),c_0_69]),c_0_70]),c_0_169]),c_0_169]),c_0_119])]),c_0_171])).

cnf(c_0_178,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_76]),c_0_69]),c_0_70])])).

cnf(c_0_179,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_178,c_0_81])).

cnf(c_0_180,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_87]),c_0_70])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:31:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.53/0.75  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S0Y
% 0.53/0.75  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.53/0.75  #
% 0.53/0.75  # Preprocessing time       : 0.044 s
% 0.53/0.75  
% 0.53/0.75  # Proof found!
% 0.53/0.75  # SZS status Theorem
% 0.53/0.75  # SZS output start CNFRefutation
% 0.53/0.75  fof(t64_pre_topc, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_pre_topc)).
% 0.53/0.75  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.53/0.75  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.53/0.75  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.53/0.75  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.53/0.75  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.53/0.75  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.53/0.75  fof(t63_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_pre_topc)).
% 0.53/0.75  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.53/0.75  fof(t62_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_pre_topc)).
% 0.53/0.75  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.53/0.75  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.53/0.75  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.53/0.75  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.53/0.75  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.53/0.75  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.53/0.75  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.53/0.75  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.53/0.75  fof(rc1_funct_2, axiom, ![X1, X2]:?[X3]:(((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&v1_relat_1(X3))&v4_relat_1(X3,X1))&v5_relat_1(X3,X2))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 0.53/0.75  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.53/0.75  fof(cc6_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&~(v1_xboole_0(X3)))&v1_funct_2(X3,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 0.53/0.75  fof(c_0_21, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))))), inference(assume_negation,[status(cth)],[t64_pre_topc])).
% 0.53/0.75  fof(c_0_22, negated_conjecture, ((v2_pre_topc(esk4_0)&l1_pre_topc(esk4_0))&((v2_pre_topc(esk5_0)&l1_pre_topc(esk5_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))))&(esk6_0=esk7_0&((~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))&(v5_pre_topc(esk6_0,esk4_0,esk5_0)|v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.53/0.75  fof(c_0_23, plain, ![X31, X32, X33]:((v1_funct_1(X33)|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|v1_xboole_0(X32))&(v1_partfun1(X33,X31)|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|v1_xboole_0(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.53/0.75  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.75  cnf(c_0_25, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.75  cnf(c_0_26, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.75  fof(c_0_27, plain, ![X25, X26, X27]:((v4_relat_1(X27,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(v5_relat_1(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.53/0.75  fof(c_0_28, plain, ![X20, X21]:(~v1_relat_1(X20)|(~m1_subset_1(X21,k1_zfmisc_1(X20))|v1_relat_1(X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.53/0.75  fof(c_0_29, plain, ![X22, X23]:v1_relat_1(k2_zfmisc_1(X22,X23)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.53/0.75  fof(c_0_30, plain, ![X28, X29, X30]:(~v1_xboole_0(X28)|(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X28)))|v1_xboole_0(X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.53/0.75  fof(c_0_31, plain, ![X37, X38]:((~v1_partfun1(X38,X37)|k1_relat_1(X38)=X37|(~v1_relat_1(X38)|~v4_relat_1(X38,X37)))&(k1_relat_1(X38)!=X37|v1_partfun1(X38,X37)|(~v1_relat_1(X38)|~v4_relat_1(X38,X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.53/0.75  cnf(c_0_32, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.75  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.53/0.75  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(rw,[status(thm)],[c_0_26, c_0_25])).
% 0.53/0.75  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.75  cnf(c_0_36, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.53/0.75  cnf(c_0_37, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.53/0.75  cnf(c_0_38, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.53/0.75  fof(c_0_39, plain, ![X50, X51, X52, X53]:((~v5_pre_topc(X52,X50,X51)|v5_pre_topc(X53,X50,g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))|X52!=X53|(~v1_funct_1(X53)|~v1_funct_2(X53,u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51))))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))))))|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|(~v2_pre_topc(X51)|~l1_pre_topc(X51))|(~v2_pre_topc(X50)|~l1_pre_topc(X50)))&(~v5_pre_topc(X53,X50,g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))|v5_pre_topc(X52,X50,X51)|X52!=X53|(~v1_funct_1(X53)|~v1_funct_2(X53,u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51))))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))))))|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|(~v2_pre_topc(X51)|~l1_pre_topc(X51))|(~v2_pre_topc(X50)|~l1_pre_topc(X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).
% 0.53/0.75  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.75  cnf(c_0_41, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.75  cnf(c_0_42, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.53/0.75  cnf(c_0_43, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.53/0.75  cnf(c_0_44, negated_conjecture, (v1_partfun1(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))|v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])])).
% 0.53/0.75  cnf(c_0_45, negated_conjecture, (v4_relat_1(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))), inference(spm,[status(thm)],[c_0_36, c_0_33])).
% 0.53/0.75  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_38])])).
% 0.53/0.75  cnf(c_0_47, plain, (v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.53/0.75  cnf(c_0_48, negated_conjecture, (v1_partfun1(esk6_0,u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_40]), c_0_41]), c_0_35])])).
% 0.53/0.75  cnf(c_0_49, negated_conjecture, (v4_relat_1(esk6_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_40])).
% 0.53/0.75  cnf(c_0_50, negated_conjecture, (v1_xboole_0(esk6_0)|~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(spm,[status(thm)],[c_0_42, c_0_33])).
% 0.53/0.75  cnf(c_0_51, negated_conjecture, (k1_relat_1(esk6_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])])).
% 0.53/0.75  cnf(c_0_52, negated_conjecture, (~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.75  cnf(c_0_53, plain, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_47])).
% 0.53/0.75  cnf(c_0_54, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.75  cnf(c_0_55, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.75  fof(c_0_56, plain, ![X15]:(~v1_xboole_0(X15)|X15=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.53/0.75  cnf(c_0_57, negated_conjecture, (k1_relat_1(esk6_0)=u1_struct_0(esk4_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_48]), c_0_49]), c_0_46])])).
% 0.53/0.75  cnf(c_0_58, negated_conjecture, (k1_relat_1(esk6_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.53/0.75  cnf(c_0_59, negated_conjecture, (v1_xboole_0(esk6_0)|~v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_42, c_0_40])).
% 0.53/0.75  fof(c_0_60, plain, ![X46, X47, X48, X49]:((~v5_pre_topc(X48,X46,X47)|v5_pre_topc(X49,g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46)),X47)|X48!=X49|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X47))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X47)))))|(~v2_pre_topc(X47)|~l1_pre_topc(X47))|(~v2_pre_topc(X46)|~l1_pre_topc(X46)))&(~v5_pre_topc(X49,g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46)),X47)|v5_pre_topc(X48,X46,X47)|X48!=X49|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X47))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X47)))))|(~v2_pre_topc(X47)|~l1_pre_topc(X47))|(~v2_pre_topc(X46)|~l1_pre_topc(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).
% 0.53/0.75  cnf(c_0_61, negated_conjecture, (~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_52, c_0_25])).
% 0.53/0.75  cnf(c_0_62, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_33]), c_0_54]), c_0_55]), c_0_34]), c_0_35])])).
% 0.53/0.75  cnf(c_0_63, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.53/0.75  cnf(c_0_64, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|v1_xboole_0(esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 0.53/0.75  cnf(c_0_65, plain, (v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.53/0.75  cnf(c_0_66, negated_conjecture, (~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.53/0.75  cnf(c_0_67, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.53/0.75  cnf(c_0_68, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_65])).
% 0.53/0.75  cnf(c_0_69, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.75  cnf(c_0_70, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.75  cnf(c_0_71, negated_conjecture, (esk6_0=k1_xboole_0|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_41]), c_0_40])])).
% 0.53/0.75  cnf(c_0_72, negated_conjecture, (esk6_0=k1_xboole_0|v5_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),X2)|~v5_pre_topc(X1,esk4_0,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(X2))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_67]), c_0_69]), c_0_70])])).
% 0.53/0.75  fof(c_0_73, plain, ![X45]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)))|(~v2_pre_topc(X45)|~l1_pre_topc(X45)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)))|(~v2_pre_topc(X45)|~l1_pre_topc(X45)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.53/0.75  cnf(c_0_74, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.53/0.75  cnf(c_0_75, negated_conjecture, (esk6_0=k1_xboole_0|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_54]), c_0_55]), c_0_41]), c_0_35]), c_0_40])])).
% 0.53/0.75  cnf(c_0_76, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.53/0.75  fof(c_0_77, plain, ![X42, X43]:((v1_pre_topc(g1_pre_topc(X42,X43))|~m1_subset_1(X43,k1_zfmisc_1(k1_zfmisc_1(X42))))&(l1_pre_topc(g1_pre_topc(X42,X43))|~m1_subset_1(X43,k1_zfmisc_1(k1_zfmisc_1(X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.53/0.75  cnf(c_0_78, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_74])).
% 0.53/0.75  cnf(c_0_79, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk5_0)|v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.75  cnf(c_0_80, negated_conjecture, (esk6_0=k1_xboole_0|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_69]), c_0_70])])).
% 0.53/0.75  cnf(c_0_81, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.53/0.75  fof(c_0_82, plain, ![X44]:(~l1_pre_topc(X44)|m1_subset_1(u1_pre_topc(X44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X44))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.53/0.75  cnf(c_0_83, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.53/0.75  cnf(c_0_84, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_33]), c_0_54]), c_0_55]), c_0_34]), c_0_35])])).
% 0.53/0.75  cnf(c_0_85, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_79, c_0_25])).
% 0.53/0.75  cnf(c_0_86, negated_conjecture, (esk6_0=k1_xboole_0|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.53/0.75  cnf(c_0_87, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.53/0.75  cnf(c_0_88, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_83])).
% 0.53/0.75  cnf(c_0_89, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.53/0.75  cnf(c_0_90, negated_conjecture, (esk6_0=k1_xboole_0|~v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_70])])).
% 0.53/0.75  fof(c_0_91, plain, ![X16, X17]:((k2_zfmisc_1(X16,X17)!=k1_xboole_0|(X16=k1_xboole_0|X17=k1_xboole_0))&((X16!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0)&(X17!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.53/0.75  cnf(c_0_92, negated_conjecture, (esk6_0=k1_xboole_0|v5_pre_topc(X1,esk4_0,X2)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(X2))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_67]), c_0_69]), c_0_70])])).
% 0.53/0.75  cnf(c_0_93, negated_conjecture, (esk6_0=k1_xboole_0|v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_67]), c_0_41]), c_0_40])]), c_0_90])).
% 0.53/0.75  fof(c_0_94, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.53/0.75  fof(c_0_95, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.53/0.75  cnf(c_0_96, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.53/0.75  cnf(c_0_97, negated_conjecture, (esk6_0=k1_xboole_0|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_54]), c_0_55]), c_0_41]), c_0_35]), c_0_40])]), c_0_90])).
% 0.53/0.75  fof(c_0_98, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.53/0.75  cnf(c_0_99, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.53/0.75  cnf(c_0_100, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.53/0.75  cnf(c_0_101, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_96]), c_0_63])).
% 0.53/0.75  cnf(c_0_102, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.53/0.75  fof(c_0_103, plain, ![X39, X40]:(((((m1_subset_1(esk3_2(X39,X40),k1_zfmisc_1(k2_zfmisc_1(X39,X40)))&v1_relat_1(esk3_2(X39,X40)))&v4_relat_1(esk3_2(X39,X40),X39))&v5_relat_1(esk3_2(X39,X40),X40))&v1_funct_1(esk3_2(X39,X40)))&v1_funct_2(esk3_2(X39,X40),X39,X40)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).
% 0.53/0.75  cnf(c_0_104, negated_conjecture, (esk6_0=k1_xboole_0|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_76]), c_0_69]), c_0_70])])).
% 0.53/0.75  cnf(c_0_105, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.53/0.75  cnf(c_0_106, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.53/0.75  cnf(c_0_107, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.53/0.75  cnf(c_0_108, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.53/0.75  cnf(c_0_109, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.53/0.75  fof(c_0_110, plain, ![X24]:(~v1_xboole_0(X24)|v1_funct_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.53/0.75  cnf(c_0_111, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_33]), c_0_69]), c_0_70]), c_0_34]), c_0_35])])).
% 0.53/0.75  cnf(c_0_112, negated_conjecture, (esk6_0=k1_xboole_0|~m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_104, c_0_81])).
% 0.53/0.75  cnf(c_0_113, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.53/0.75  cnf(c_0_114, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_63, c_0_107])).
% 0.53/0.75  cnf(c_0_115, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(k1_xboole_0))|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.53/0.75  cnf(c_0_116, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_110])).
% 0.53/0.75  cnf(c_0_117, negated_conjecture, (~v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(spm,[status(thm)],[c_0_61, c_0_111])).
% 0.53/0.75  cnf(c_0_118, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_87]), c_0_70])])).
% 0.53/0.75  cnf(c_0_119, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_113, c_0_102])).
% 0.53/0.75  cnf(c_0_120, plain, (v1_funct_2(esk3_2(X1,X2),X1,X2)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.53/0.75  cnf(c_0_121, plain, (esk3_2(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 0.53/0.75  cnf(c_0_122, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_113, c_0_107])).
% 0.53/0.75  cnf(c_0_123, plain, (v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_116, c_0_107])).
% 0.53/0.75  cnf(c_0_124, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_118]), c_0_118]), c_0_118]), c_0_118]), c_0_119])])).
% 0.53/0.75  cnf(c_0_125, plain, (v1_funct_2(k1_xboole_0,X1,X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 0.53/0.75  cnf(c_0_126, plain, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|u1_struct_0(X2)!=k1_xboole_0|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_109]), c_0_122]), c_0_123])).
% 0.53/0.75  cnf(c_0_127, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 0.53/0.75  cnf(c_0_128, plain, (v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|u1_struct_0(X1)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,X1,X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_125]), c_0_119])]), c_0_125])).
% 0.53/0.75  cnf(c_0_129, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_54]), c_0_69]), c_0_55]), c_0_70])])).
% 0.53/0.75  fof(c_0_130, plain, ![X34, X35, X36]:(((v1_funct_1(X36)|(~v1_funct_1(X36)|~v1_funct_2(X36,X34,X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|(v1_xboole_0(X34)|v1_xboole_0(X35)))&(~v1_xboole_0(X36)|(~v1_funct_1(X36)|~v1_funct_2(X36,X34,X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|(v1_xboole_0(X34)|v1_xboole_0(X35))))&(v1_funct_2(X36,X34,X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,X34,X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|(v1_xboole_0(X34)|v1_xboole_0(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).
% 0.53/0.75  cnf(c_0_131, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_33]), c_0_69]), c_0_70]), c_0_34]), c_0_35])])).
% 0.53/0.75  cnf(c_0_132, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_76]), c_0_54]), c_0_55])])).
% 0.53/0.75  cnf(c_0_133, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(k1_xboole_0))|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_108, c_0_96])).
% 0.53/0.75  cnf(c_0_134, plain, (v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_130])).
% 0.53/0.75  cnf(c_0_135, plain, (v1_funct_1(esk3_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.53/0.75  cnf(c_0_136, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(spm,[status(thm)],[c_0_131, c_0_85])).
% 0.53/0.75  cnf(c_0_137, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_132, c_0_81])).
% 0.53/0.75  cnf(c_0_138, plain, (esk3_2(X1,X2)=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_114, c_0_133])).
% 0.53/0.75  cnf(c_0_139, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_116, c_0_102])).
% 0.53/0.75  cnf(c_0_140, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X3)), inference(csr,[status(thm)],[c_0_134, c_0_116])).
% 0.53/0.75  cnf(c_0_141, plain, (v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),X1,X2)|~v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v1_funct_2(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_108]), c_0_120]), c_0_135])])).
% 0.53/0.75  cnf(c_0_142, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_136, c_0_118]), c_0_118]), c_0_118]), c_0_118]), c_0_119])])).
% 0.53/0.75  cnf(c_0_143, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_87]), c_0_55])])).
% 0.53/0.75  cnf(c_0_144, negated_conjecture, (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_118]), c_0_118]), c_0_118]), c_0_118]), c_0_119])])).
% 0.53/0.75  cnf(c_0_145, plain, (v1_funct_2(k1_xboole_0,X1,X2)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_120, c_0_138])).
% 0.53/0.75  cnf(c_0_146, plain, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~v5_pre_topc(k1_xboole_0,X1,X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))|~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_119]), c_0_139]), c_0_119])])).
% 0.53/0.75  cnf(c_0_147, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|~v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_40]), c_0_41])])).
% 0.53/0.75  cnf(c_0_148, plain, (v5_pre_topc(k1_xboole_0,X1,X2)|u1_struct_0(X1)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_121]), c_0_119])]), c_0_125])).
% 0.53/0.75  cnf(c_0_149, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|u1_struct_0(esk4_0)!=k1_xboole_0|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_125]), c_0_143])).
% 0.53/0.75  cnf(c_0_150, negated_conjecture, (u1_struct_0(esk5_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(spm,[status(thm)],[c_0_144, c_0_145])).
% 0.53/0.75  cnf(c_0_151, plain, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|u1_struct_0(X2)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,X1,X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_145]), c_0_145])).
% 0.53/0.75  cnf(c_0_152, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v1_xboole_0(u1_struct_0(esk4_0))|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_63, c_0_147])).
% 0.53/0.75  cnf(c_0_153, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_149]), c_0_54]), c_0_69]), c_0_55]), c_0_70])]), c_0_143])).
% 0.53/0.75  cnf(c_0_154, negated_conjecture, (u1_struct_0(esk5_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_151]), c_0_54]), c_0_69]), c_0_55]), c_0_70])])).
% 0.53/0.75  cnf(c_0_155, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|u1_struct_0(esk4_0)=k1_xboole_0|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_63, c_0_152])).
% 0.53/0.75  cnf(c_0_156, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_76]), c_0_54]), c_0_55])])).
% 0.53/0.75  cnf(c_0_157, plain, (v1_xboole_0(esk3_2(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_42, c_0_108])).
% 0.53/0.75  cnf(c_0_158, negated_conjecture, (u1_struct_0(esk5_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_76]), c_0_69]), c_0_70])])).
% 0.53/0.75  cnf(c_0_159, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|u1_struct_0(esk5_0)=k1_xboole_0|~m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_155, c_0_107])).
% 0.53/0.75  cnf(c_0_160, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_156, c_0_81])).
% 0.53/0.75  cnf(c_0_161, plain, (esk3_2(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_63, c_0_157])).
% 0.53/0.75  cnf(c_0_162, negated_conjecture, (u1_struct_0(esk5_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_158, c_0_81])).
% 0.53/0.75  cnf(c_0_163, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|u1_struct_0(esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_159, c_0_118]), c_0_119])])).
% 0.53/0.75  cnf(c_0_164, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_87]), c_0_55])])).
% 0.53/0.75  cnf(c_0_165, plain, (v1_funct_2(k1_xboole_0,X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_120, c_0_161])).
% 0.53/0.75  cnf(c_0_166, negated_conjecture, (u1_struct_0(esk5_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_87]), c_0_70])])).
% 0.53/0.75  cnf(c_0_167, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_163, c_0_164])).
% 0.53/0.75  cnf(c_0_168, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_118]), c_0_118]), c_0_118]), c_0_118]), c_0_119])])).
% 0.53/0.75  cnf(c_0_169, plain, (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_165, c_0_102])).
% 0.53/0.75  cnf(c_0_170, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_118]), c_0_118])).
% 0.53/0.75  cnf(c_0_171, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_166, c_0_167])])).
% 0.53/0.75  cnf(c_0_172, plain, (v5_pre_topc(X1,X2,X3)|u1_struct_0(X3)!=k1_xboole_0|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_96]), c_0_122]), c_0_123])).
% 0.53/0.75  cnf(c_0_173, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_168, c_0_167]), c_0_167]), c_0_169])])).
% 0.53/0.75  cnf(c_0_174, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_170, c_0_167]), c_0_171])).
% 0.53/0.75  cnf(c_0_175, negated_conjecture, (v5_pre_topc(X1,X2,esk5_0)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),esk5_0)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),k1_xboole_0)|~v1_funct_2(X1,u1_struct_0(X2),k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172, c_0_167]), c_0_54]), c_0_55])])).
% 0.53/0.75  cnf(c_0_176, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_173, c_0_174])])).
% 0.53/0.75  cnf(c_0_177, negated_conjecture, (~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_176]), c_0_69]), c_0_70]), c_0_169]), c_0_169]), c_0_119])]), c_0_171])).
% 0.53/0.75  cnf(c_0_178, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177, c_0_76]), c_0_69]), c_0_70])])).
% 0.53/0.75  cnf(c_0_179, negated_conjecture, (~m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_178, c_0_81])).
% 0.53/0.75  cnf(c_0_180, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_87]), c_0_70])]), ['proof']).
% 0.53/0.75  # SZS output end CNFRefutation
% 0.53/0.75  # Proof object total steps             : 181
% 0.53/0.75  # Proof object clause steps            : 139
% 0.53/0.75  # Proof object formula steps           : 42
% 0.53/0.75  # Proof object conjectures             : 86
% 0.53/0.75  # Proof object clause conjectures      : 83
% 0.53/0.75  # Proof object formula conjectures     : 3
% 0.53/0.75  # Proof object initial clauses used    : 37
% 0.53/0.75  # Proof object initial formulas used   : 21
% 0.53/0.75  # Proof object generating inferences   : 82
% 0.53/0.75  # Proof object simplifying inferences  : 187
% 0.53/0.75  # Training examples: 0 positive, 0 negative
% 0.53/0.75  # Parsed axioms                        : 21
% 0.53/0.75  # Removed by relevancy pruning/SinE    : 0
% 0.53/0.75  # Initial clauses                      : 53
% 0.53/0.75  # Removed in clause preprocessing      : 3
% 0.53/0.75  # Initial clauses in saturation        : 50
% 0.53/0.75  # Processed clauses                    : 1701
% 0.53/0.75  # ...of these trivial                  : 35
% 0.53/0.75  # ...subsumed                          : 733
% 0.53/0.75  # ...remaining for further processing  : 933
% 0.53/0.75  # Other redundant clauses eliminated   : 41
% 0.53/0.75  # Clauses deleted for lack of memory   : 0
% 0.53/0.75  # Backward-subsumed                    : 203
% 0.53/0.75  # Backward-rewritten                   : 449
% 0.53/0.75  # Generated clauses                    : 8639
% 0.53/0.75  # ...of the previous two non-trivial   : 7657
% 0.53/0.75  # Contextual simplify-reflections      : 160
% 0.53/0.75  # Paramodulations                      : 8567
% 0.53/0.75  # Factorizations                       : 5
% 0.53/0.75  # Equation resolutions                 : 53
% 0.53/0.75  # Propositional unsat checks           : 0
% 0.53/0.75  #    Propositional check models        : 0
% 0.53/0.75  #    Propositional check unsatisfiable : 0
% 0.53/0.75  #    Propositional clauses             : 0
% 0.53/0.75  #    Propositional clauses after purity: 0
% 0.53/0.75  #    Propositional unsat core size     : 0
% 0.53/0.75  #    Propositional preprocessing time  : 0.000
% 0.53/0.75  #    Propositional encoding time       : 0.000
% 0.53/0.75  #    Propositional solver time         : 0.000
% 0.53/0.75  #    Success case prop preproc time    : 0.000
% 0.53/0.75  #    Success case prop encoding time   : 0.000
% 0.53/0.75  #    Success case prop solver time     : 0.000
% 0.53/0.75  # Current number of processed clauses  : 263
% 0.53/0.75  #    Positive orientable unit clauses  : 37
% 0.53/0.75  #    Positive unorientable unit clauses: 0
% 0.53/0.75  #    Negative unit clauses             : 5
% 0.53/0.75  #    Non-unit-clauses                  : 221
% 0.53/0.75  # Current number of unprocessed clauses: 3274
% 0.53/0.75  # ...number of literals in the above   : 29097
% 0.53/0.75  # Current number of archived formulas  : 0
% 0.53/0.75  # Current number of archived clauses   : 666
% 0.53/0.75  # Clause-clause subsumption calls (NU) : 319607
% 0.53/0.75  # Rec. Clause-clause subsumption calls : 34975
% 0.53/0.75  # Non-unit clause-clause subsumptions  : 1020
% 0.53/0.75  # Unit Clause-clause subsumption calls : 1591
% 0.53/0.75  # Rewrite failures with RHS unbound    : 0
% 0.53/0.75  # BW rewrite match attempts            : 41
% 0.53/0.75  # BW rewrite match successes           : 11
% 0.53/0.75  # Condensation attempts                : 0
% 0.53/0.75  # Condensation successes               : 0
% 0.53/0.75  # Termbank termtop insertions          : 422974
% 0.53/0.75  
% 0.53/0.75  # -------------------------------------------------
% 0.53/0.75  # User time                : 0.401 s
% 0.53/0.75  # System time              : 0.014 s
% 0.53/0.75  # Total time               : 0.415 s
% 0.53/0.75  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
