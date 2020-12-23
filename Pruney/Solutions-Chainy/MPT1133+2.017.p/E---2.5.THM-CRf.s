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
% DateTime   : Thu Dec  3 11:09:24 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  164 (123543 expanded)
%              Number of clauses        :  126 (47832 expanded)
%              Number of leaves         :   19 (28464 expanded)
%              Depth                    :   28
%              Number of atoms          :  698 (981280 expanded)
%              Number of equality atoms :   58 (74432 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   4 average)
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

fof(t13_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( r1_tarski(k1_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t14_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_tarski(k2_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

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
    ! [X52,X53,X54,X55] :
      ( ( ~ v5_pre_topc(X54,X52,X53)
        | v5_pre_topc(X55,X52,g1_pre_topc(u1_struct_0(X53),u1_pre_topc(X53)))
        | X54 != X55
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,u1_struct_0(X52),u1_struct_0(g1_pre_topc(u1_struct_0(X53),u1_pre_topc(X53))))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(g1_pre_topc(u1_struct_0(X53),u1_pre_topc(X53))))))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53))))
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) )
      & ( ~ v5_pre_topc(X55,X52,g1_pre_topc(u1_struct_0(X53),u1_pre_topc(X53)))
        | v5_pre_topc(X54,X52,X53)
        | X54 != X55
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,u1_struct_0(X52),u1_struct_0(g1_pre_topc(u1_struct_0(X53),u1_pre_topc(X53))))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(g1_pre_topc(u1_struct_0(X53),u1_pre_topc(X53))))))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53))))
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).

fof(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))
    & esk4_0 = esk5_0
    & ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
      | ~ v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) )
    & ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
      | v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_22,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
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
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_33,plain,(
    ! [X25,X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X27)))
      | ~ r1_tarski(k1_relat_1(X28),X26)
      | m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).

fof(c_0_34,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | v1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_35,negated_conjecture,
    ( v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | ~ v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_36,negated_conjecture,
    ( v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_24])).

fof(c_0_37,plain,(
    ! [X47] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X47),u1_pre_topc(X47)))
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X47),u1_pre_topc(X47)))
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k1_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_40,plain,(
    ! [X15,X16] :
      ( ( ~ v4_relat_1(X16,X15)
        | r1_tarski(k1_relat_1(X16),X15)
        | ~ v1_relat_1(X16) )
      & ( ~ r1_tarski(k1_relat_1(X16),X15)
        | v4_relat_1(X16,X15)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_41,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X41,X42,X43] :
      ( ( X42 = k1_xboole_0
        | v1_partfun1(X43,X41)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X41,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( X41 != k1_xboole_0
        | v1_partfun1(X43,X41)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X41,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

cnf(c_0_43,negated_conjecture,
    ( v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_47,plain,(
    ! [X44,X45] :
      ( ( v1_pre_topc(g1_pre_topc(X44,X45))
        | ~ m1_subset_1(X45,k1_zfmisc_1(k1_zfmisc_1(X44))) )
      & ( l1_pre_topc(g1_pre_topc(X44,X45))
        | ~ m1_subset_1(X45,k1_zfmisc_1(k1_zfmisc_1(X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

fof(c_0_48,plain,(
    ! [X38,X39,X40] :
      ( ( v1_funct_1(X40)
        | ~ v1_funct_1(X40)
        | ~ v1_partfun1(X40,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v1_funct_2(X40,X38,X39)
        | ~ v1_funct_1(X40)
        | ~ v1_partfun1(X40,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))
    | ~ r1_tarski(k1_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_53,plain,(
    ! [X22,X23,X24] :
      ( ( v4_relat_1(X24,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v5_relat_1(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_54,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_55,plain,(
    ! [X48,X49,X50,X51] :
      ( ( ~ v5_pre_topc(X50,X48,X49)
        | v5_pre_topc(X51,g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48)),X49)
        | X50 != X51
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48))),u1_struct_0(X49))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48))),u1_struct_0(X49))))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,u1_struct_0(X48),u1_struct_0(X49))
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X49))))
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( ~ v5_pre_topc(X51,g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48)),X49)
        | v5_pre_topc(X50,X48,X49)
        | X50 != X51
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48))),u1_struct_0(X49))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48))),u1_struct_0(X49))))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,u1_struct_0(X48),u1_struct_0(X49))
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X49))))
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).

cnf(c_0_56,negated_conjecture,
    ( v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_57,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_58,plain,(
    ! [X46] :
      ( ~ l1_pre_topc(X46)
      | m1_subset_1(u1_pre_topc(X46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X46)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_59,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))
    | ~ v4_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_64,plain,
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
    inference(er,[status(thm)],[c_0_54])).

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
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_67,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_2(esk4_0,X1,u1_struct_0(esk3_0))
    | ~ v1_partfun1(esk4_0,X1)
    | ~ v4_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_31])])).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0
    | v1_partfun1(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_27]),c_0_30]),c_0_31])])).

cnf(c_0_70,negated_conjecture,
    ( v4_relat_1(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_27])).

cnf(c_0_71,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_24])).

cnf(c_0_72,negated_conjecture,
    ( v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_73,plain,
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

cnf(c_0_74,negated_conjecture,
    ( v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_46])])).

cnf(c_0_75,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0
    | v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])).

cnf(c_0_76,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk3_0)
    | ~ v5_pre_topc(esk4_0,X1,esk3_0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(esk3_0))
    | ~ v1_funct_2(esk4_0,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v4_relat_1(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_60]),c_0_28]),c_0_29]),c_0_31])])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_79,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0
    | v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_60]),c_0_70])])).

cnf(c_0_81,negated_conjecture,
    ( v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_70]),c_0_45]),c_0_46]),c_0_78]),c_0_39])])).

cnf(c_0_82,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0
    | v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_60]),c_0_70])])).

fof(c_0_83,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X29)))
      | ~ r1_tarski(k2_relat_1(X32),X30)
      | m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).

cnf(c_0_84,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0
    | ~ v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0
    | v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_75]),c_0_82])).

cnf(c_0_86,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

fof(c_0_87,plain,(
    ! [X17,X18] :
      ( ( ~ v5_relat_1(X18,X17)
        | r1_tarski(k2_relat_1(X18),X17)
        | ~ v1_relat_1(X18) )
      & ( ~ r1_tarski(k2_relat_1(X18),X17)
        | v5_relat_1(X18,X17)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_88,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(esk4_0),X2)
    | ~ v4_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_60])).

cnf(c_0_90,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_91,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),X1)))
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_39])).

cnf(c_0_93,negated_conjecture,
    ( v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_27]),c_0_45]),c_0_46]),c_0_30]),c_0_31])])).

cnf(c_0_94,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_44]),c_0_45]),c_0_46])])).

fof(c_0_95,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v5_relat_1(esk4_0,X2)
    | ~ v4_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_51])])).

cnf(c_0_97,negated_conjecture,
    ( v5_relat_1(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_27])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),X1)))
    | ~ v5_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_90]),c_0_51])])).

cnf(c_0_99,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_93])).

cnf(c_0_100,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_57])).

cnf(c_0_101,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_102,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))
    | ~ v4_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v5_pre_topc(esk4_0,esk2_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ v5_relat_1(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X1)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_98]),c_0_45]),c_0_46]),c_0_31])])).

cnf(c_0_105,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_98]),c_0_97])])).

cnf(c_0_106,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_67]),c_0_46])])).

cnf(c_0_107,plain,
    ( v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))) != k1_xboole_0
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_101])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_101])).

fof(c_0_109,plain,(
    ! [X12,X13,X14] :
      ( ~ r2_hidden(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X14))
      | ~ v1_xboole_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_110,plain,
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
    inference(er,[status(thm)],[c_0_102])).

cnf(c_0_111,negated_conjecture,
    ( v1_funct_2(esk4_0,X1,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    | ~ v1_partfun1(esk4_0,X1)
    | ~ v4_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_103]),c_0_31])])).

cnf(c_0_112,negated_conjecture,
    ( v4_relat_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_39])).

cnf(c_0_113,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_97]),c_0_28]),c_0_29]),c_0_78]),c_0_39])])).

cnf(c_0_114,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_115,negated_conjecture,
    ( v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v5_pre_topc(X1,X2,esk3_0)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(X2),k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_106]),c_0_28]),c_0_29])])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_106])).

cnf(c_0_117,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_118,negated_conjecture,
    ( v5_pre_topc(esk4_0,X1,esk3_0)
    | ~ v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk3_0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(esk3_0))
    | ~ v1_funct_2(esk4_0,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v4_relat_1(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_60]),c_0_28]),c_0_29]),c_0_31])])).

cnf(c_0_119,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_27]),c_0_45]),c_0_46]),c_0_30]),c_0_31])])).

cnf(c_0_120,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_partfun1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_111]),c_0_112])])).

cnf(c_0_121,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v1_partfun1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_111]),c_0_112])])).

cnf(c_0_122,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_45]),c_0_46]),c_0_78]),c_0_31]),c_0_39])]),c_0_116])).

cnf(c_0_123,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) ),
    inference(spm,[status(thm)],[c_0_117,c_0_27])).

cnf(c_0_124,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_125,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_70]),c_0_45]),c_0_46]),c_0_78]),c_0_39])])).

cnf(c_0_126,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(spm,[status(thm)],[c_0_119,c_0_36])).

cnf(c_0_127,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_partfun1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_128,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_44]),c_0_28]),c_0_29])])).

cnf(c_0_129,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) != k1_xboole_0
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_101]),c_0_124])])).

cnf(c_0_130,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_75]),c_0_85]),c_0_106])).

fof(c_0_131,plain,(
    ! [X33,X35,X36,X37] :
      ( ( r2_hidden(esk1_1(X33),X33)
        | X33 = k1_xboole_0 )
      & ( ~ r2_hidden(X35,X33)
        | esk1_1(X33) != k3_mcart_1(X35,X36,X37)
        | X33 = k1_xboole_0 )
      & ( ~ r2_hidden(X36,X33)
        | esk1_1(X33) != k3_mcart_1(X35,X36,X37)
        | X33 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_132,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_44]),c_0_28]),c_0_29])])).

cnf(c_0_133,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_partfun1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_44]),c_0_28]),c_0_29])])).

cnf(c_0_134,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),k1_xboole_0)
    | ~ m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_128,c_0_57])).

cnf(c_0_135,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_130])])).

cnf(c_0_136,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_131])).

cnf(c_0_137,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))
    | ~ m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_132,c_0_57])).

cnf(c_0_138,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v1_partfun1(esk4_0,u1_struct_0(esk2_0))
    | ~ m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_57])).

fof(c_0_139,plain,(
    ! [X8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_140,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,X1)
    | ~ v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ v5_relat_1(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X1)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_98]),c_0_45]),c_0_46]),c_0_31])])).

cnf(c_0_141,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_67]),c_0_29])])).

cnf(c_0_142,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_143,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_67]),c_0_29])])).

cnf(c_0_144,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v1_partfun1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_67]),c_0_29])])).

cnf(c_0_145,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_139])).

cnf(c_0_146,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_97]),c_0_28]),c_0_29]),c_0_78]),c_0_39])])).

cnf(c_0_147,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk2_0,esk3_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk2_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_141,c_0_142]),c_0_142])).

cnf(c_0_148,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v1_partfun1(esk4_0,u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_111]),c_0_112])])).

cnf(c_0_149,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk2_0,esk3_0)
    | ~ v1_partfun1(k1_xboole_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_144,c_0_142]),c_0_142])).

cnf(c_0_150,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_145])).

cnf(c_0_151,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v1_partfun1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_39]),c_0_78]),c_0_31])])).

cnf(c_0_152,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk2_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_146,c_0_130]),c_0_142]),c_0_142]),c_0_142]),c_0_147])).

cnf(c_0_153,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_partfun1(k1_xboole_0,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_148,c_0_130]),c_0_142]),c_0_142]),c_0_142]),c_0_142]),c_0_145])]),c_0_149])).

cnf(c_0_154,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_130]),c_0_142]),c_0_142]),c_0_142]),c_0_150])])).

cnf(c_0_155,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v1_partfun1(k1_xboole_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_151,c_0_142])).

cnf(c_0_156,negated_conjecture,
    ( ~ v1_partfun1(k1_xboole_0,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_154])).

cnf(c_0_157,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_155,c_0_156])).

cnf(c_0_158,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_78,c_0_142])).

cnf(c_0_159,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk2_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk2_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_152,c_0_157])).

cnf(c_0_160,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(esk2_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_158,c_0_157])).

cnf(c_0_161,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk2_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_159,c_0_160])])).

cnf(c_0_162,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_147,c_0_160])])).

cnf(c_0_163,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_143,c_0_130]),c_0_130]),c_0_142]),c_0_157]),c_0_142]),c_0_142]),c_0_160]),c_0_142]),c_0_145])]),c_0_161]),c_0_162]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.38/0.60  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.38/0.60  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.38/0.60  #
% 0.38/0.60  # Preprocessing time       : 0.044 s
% 0.38/0.60  
% 0.38/0.60  # Proof found!
% 0.38/0.60  # SZS status Theorem
% 0.38/0.60  # SZS output start CNFRefutation
% 0.38/0.60  fof(t64_pre_topc, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_pre_topc)).
% 0.38/0.60  fof(t63_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_pre_topc)).
% 0.38/0.60  fof(t13_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 0.38/0.60  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.38/0.60  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.38/0.60  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.38/0.60  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 0.38/0.60  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.38/0.60  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.38/0.60  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.38/0.60  fof(t62_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_pre_topc)).
% 0.38/0.60  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.38/0.60  fof(t14_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_tarski(k2_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 0.38/0.60  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.38/0.60  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.38/0.60  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.38/0.60  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.38/0.60  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.38/0.60  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.38/0.60  fof(c_0_19, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))))), inference(assume_negation,[status(cth)],[t64_pre_topc])).
% 0.38/0.60  fof(c_0_20, plain, ![X52, X53, X54, X55]:((~v5_pre_topc(X54,X52,X53)|v5_pre_topc(X55,X52,g1_pre_topc(u1_struct_0(X53),u1_pre_topc(X53)))|X54!=X55|(~v1_funct_1(X55)|~v1_funct_2(X55,u1_struct_0(X52),u1_struct_0(g1_pre_topc(u1_struct_0(X53),u1_pre_topc(X53))))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(g1_pre_topc(u1_struct_0(X53),u1_pre_topc(X53)))))))|(~v1_funct_1(X54)|~v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53)))))|(~v2_pre_topc(X53)|~l1_pre_topc(X53))|(~v2_pre_topc(X52)|~l1_pre_topc(X52)))&(~v5_pre_topc(X55,X52,g1_pre_topc(u1_struct_0(X53),u1_pre_topc(X53)))|v5_pre_topc(X54,X52,X53)|X54!=X55|(~v1_funct_1(X55)|~v1_funct_2(X55,u1_struct_0(X52),u1_struct_0(g1_pre_topc(u1_struct_0(X53),u1_pre_topc(X53))))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(g1_pre_topc(u1_struct_0(X53),u1_pre_topc(X53)))))))|(~v1_funct_1(X54)|~v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53)))))|(~v2_pre_topc(X53)|~l1_pre_topc(X53))|(~v2_pre_topc(X52)|~l1_pre_topc(X52)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).
% 0.38/0.60  fof(c_0_21, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))))&(esk4_0=esk5_0&((~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))&(v5_pre_topc(esk4_0,esk2_0,esk3_0)|v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.38/0.60  cnf(c_0_22, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.60  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.60  cnf(c_0_24, negated_conjecture, (esk4_0=esk5_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.60  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.60  cnf(c_0_26, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_22])).
% 0.38/0.60  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.38/0.60  cnf(c_0_28, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.60  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.60  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 0.38/0.60  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.60  cnf(c_0_32, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)|v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.60  fof(c_0_33, plain, ![X25, X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X27)))|(~r1_tarski(k1_relat_1(X28),X26)|m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).
% 0.38/0.60  fof(c_0_34, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|v1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.38/0.60  cnf(c_0_35, negated_conjecture, (v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|~v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])])).
% 0.38/0.60  cnf(c_0_36, negated_conjecture, (v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_32, c_0_24])).
% 0.38/0.60  fof(c_0_37, plain, ![X47]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X47),u1_pre_topc(X47)))|(~v2_pre_topc(X47)|~l1_pre_topc(X47)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X47),u1_pre_topc(X47)))|(~v2_pre_topc(X47)|~l1_pre_topc(X47)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.38/0.60  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k1_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.38/0.60  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.60  fof(c_0_40, plain, ![X15, X16]:((~v4_relat_1(X16,X15)|r1_tarski(k1_relat_1(X16),X15)|~v1_relat_1(X16))&(~r1_tarski(k1_relat_1(X16),X15)|v4_relat_1(X16,X15)|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.38/0.60  cnf(c_0_41, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.38/0.60  fof(c_0_42, plain, ![X41, X42, X43]:((X42=k1_xboole_0|v1_partfun1(X43,X41)|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X42)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))&(X41!=k1_xboole_0|v1_partfun1(X43,X41)|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X42)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.38/0.60  cnf(c_0_43, negated_conjecture, (v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.38/0.60  cnf(c_0_44, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.38/0.60  cnf(c_0_45, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.60  cnf(c_0_46, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.60  fof(c_0_47, plain, ![X44, X45]:((v1_pre_topc(g1_pre_topc(X44,X45))|~m1_subset_1(X45,k1_zfmisc_1(k1_zfmisc_1(X44))))&(l1_pre_topc(g1_pre_topc(X44,X45))|~m1_subset_1(X45,k1_zfmisc_1(k1_zfmisc_1(X44))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.38/0.60  fof(c_0_48, plain, ![X38, X39, X40]:((v1_funct_1(X40)|(~v1_funct_1(X40)|~v1_partfun1(X40,X38))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(v1_funct_2(X40,X38,X39)|(~v1_funct_1(X40)|~v1_partfun1(X40,X38))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.38/0.60  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))|~r1_tarski(k1_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.38/0.60  cnf(c_0_50, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.38/0.60  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_27])).
% 0.38/0.60  cnf(c_0_52, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.38/0.60  fof(c_0_53, plain, ![X22, X23, X24]:((v4_relat_1(X24,X22)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))&(v5_relat_1(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.38/0.60  cnf(c_0_54, plain, (v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.60  fof(c_0_55, plain, ![X48, X49, X50, X51]:((~v5_pre_topc(X50,X48,X49)|v5_pre_topc(X51,g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48)),X49)|X50!=X51|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48))),u1_struct_0(X49))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48))),u1_struct_0(X49)))))|(~v1_funct_1(X50)|~v1_funct_2(X50,u1_struct_0(X48),u1_struct_0(X49))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X49)))))|(~v2_pre_topc(X49)|~l1_pre_topc(X49))|(~v2_pre_topc(X48)|~l1_pre_topc(X48)))&(~v5_pre_topc(X51,g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48)),X49)|v5_pre_topc(X50,X48,X49)|X50!=X51|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48))),u1_struct_0(X49))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48))),u1_struct_0(X49)))))|(~v1_funct_1(X50)|~v1_funct_2(X50,u1_struct_0(X48),u1_struct_0(X49))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X49)))))|(~v2_pre_topc(X49)|~l1_pre_topc(X49))|(~v2_pre_topc(X48)|~l1_pre_topc(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).
% 0.38/0.60  cnf(c_0_56, negated_conjecture, (v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|v5_pre_topc(esk4_0,esk2_0,esk3_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])])).
% 0.38/0.60  cnf(c_0_57, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.38/0.60  fof(c_0_58, plain, ![X46]:(~l1_pre_topc(X46)|m1_subset_1(u1_pre_topc(X46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X46))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.38/0.60  cnf(c_0_59, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.38/0.60  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))|~v4_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.38/0.60  cnf(c_0_61, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_52])).
% 0.38/0.60  cnf(c_0_62, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.38/0.60  cnf(c_0_63, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.60  cnf(c_0_64, plain, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_54])).
% 0.38/0.60  cnf(c_0_65, plain, (v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.38/0.60  cnf(c_0_66, negated_conjecture, (v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))))|~m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.38/0.60  cnf(c_0_67, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.38/0.60  cnf(c_0_68, negated_conjecture, (v1_funct_2(esk4_0,X1,u1_struct_0(esk3_0))|~v1_partfun1(esk4_0,X1)|~v4_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_31])])).
% 0.38/0.60  cnf(c_0_69, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0|v1_partfun1(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_27]), c_0_30]), c_0_31])])).
% 0.38/0.60  cnf(c_0_70, negated_conjecture, (v4_relat_1(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))), inference(spm,[status(thm)],[c_0_62, c_0_27])).
% 0.38/0.60  cnf(c_0_71, negated_conjecture, (~v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_63, c_0_24])).
% 0.38/0.60  cnf(c_0_72, negated_conjecture, (v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])])).
% 0.38/0.60  cnf(c_0_73, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_65])).
% 0.38/0.60  cnf(c_0_74, negated_conjecture, (v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_46])])).
% 0.38/0.60  cnf(c_0_75, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0|v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])])).
% 0.38/0.60  cnf(c_0_76, negated_conjecture, (~v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.38/0.60  cnf(c_0_77, negated_conjecture, (v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk3_0)|~v5_pre_topc(esk4_0,X1,esk3_0)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(esk3_0))|~v1_funct_2(esk4_0,u1_struct_0(X1),u1_struct_0(esk3_0))|~v4_relat_1(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_60]), c_0_28]), c_0_29]), c_0_31])])).
% 0.38/0.60  cnf(c_0_78, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.60  cnf(c_0_79, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0|v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|v5_pre_topc(esk4_0,esk2_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.38/0.60  cnf(c_0_80, negated_conjecture, (~v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_60]), c_0_70])])).
% 0.38/0.60  cnf(c_0_81, negated_conjecture, (v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_70]), c_0_45]), c_0_46]), c_0_78]), c_0_39])])).
% 0.38/0.60  cnf(c_0_82, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0|v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_60]), c_0_70])])).
% 0.38/0.60  fof(c_0_83, plain, ![X29, X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X29)))|(~r1_tarski(k2_relat_1(X32),X30)|m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).
% 0.38/0.60  cnf(c_0_84, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0|~v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(spm,[status(thm)],[c_0_80, c_0_75])).
% 0.38/0.60  cnf(c_0_85, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0|v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_75]), c_0_82])).
% 0.38/0.60  cnf(c_0_86, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.38/0.60  fof(c_0_87, plain, ![X17, X18]:((~v5_relat_1(X18,X17)|r1_tarski(k2_relat_1(X18),X17)|~v1_relat_1(X18))&(~r1_tarski(k2_relat_1(X18),X17)|v5_relat_1(X18,X17)|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.38/0.60  cnf(c_0_88, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.38/0.60  cnf(c_0_89, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k2_relat_1(esk4_0),X2)|~v4_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_86, c_0_60])).
% 0.38/0.60  cnf(c_0_90, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.38/0.60  cnf(c_0_91, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.38/0.60  cnf(c_0_92, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),X1)))|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_86, c_0_39])).
% 0.38/0.60  cnf(c_0_93, negated_conjecture, (v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_27]), c_0_45]), c_0_46]), c_0_30]), c_0_31])])).
% 0.38/0.60  cnf(c_0_94, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_44]), c_0_45]), c_0_46])])).
% 0.38/0.60  fof(c_0_95, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.38/0.61  cnf(c_0_96, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v5_relat_1(esk4_0,X2)|~v4_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_51])])).
% 0.38/0.61  cnf(c_0_97, negated_conjecture, (v5_relat_1(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(spm,[status(thm)],[c_0_91, c_0_27])).
% 0.38/0.61  cnf(c_0_98, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),X1)))|~v5_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_90]), c_0_51])])).
% 0.38/0.61  cnf(c_0_99, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(spm,[status(thm)],[c_0_71, c_0_93])).
% 0.38/0.61  cnf(c_0_100, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_94, c_0_57])).
% 0.38/0.61  cnf(c_0_101, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.38/0.61  cnf(c_0_102, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.38/0.61  cnf(c_0_103, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))|~v4_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.38/0.61  cnf(c_0_104, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v5_pre_topc(esk4_0,esk2_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(X1))|~v5_relat_1(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X1))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_98]), c_0_45]), c_0_46]), c_0_31])])).
% 0.38/0.61  cnf(c_0_105, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_98]), c_0_97])])).
% 0.38/0.61  cnf(c_0_106, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0|~v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_67]), c_0_46])])).
% 0.38/0.61  cnf(c_0_107, plain, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))!=k1_xboole_0|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_64, c_0_101])).
% 0.38/0.61  cnf(c_0_108, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_101])).
% 0.38/0.61  fof(c_0_109, plain, ![X12, X13, X14]:(~r2_hidden(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X14))|~v1_xboole_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.38/0.61  cnf(c_0_110, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_102])).
% 0.38/0.61  cnf(c_0_111, negated_conjecture, (v1_funct_2(esk4_0,X1,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))|~v1_partfun1(esk4_0,X1)|~v4_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_103]), c_0_31])])).
% 0.38/0.61  cnf(c_0_112, negated_conjecture, (v4_relat_1(esk4_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_62, c_0_39])).
% 0.38/0.61  cnf(c_0_113, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_97]), c_0_28]), c_0_29]), c_0_78]), c_0_39])])).
% 0.38/0.61  cnf(c_0_114, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.38/0.61  cnf(c_0_115, negated_conjecture, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v5_pre_topc(X1,X2,esk3_0)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk3_0))|~v1_funct_2(X1,u1_struct_0(X2),k1_xboole_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_106]), c_0_28]), c_0_29])])).
% 0.38/0.61  cnf(c_0_116, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|~v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_108, c_0_106])).
% 0.38/0.61  cnf(c_0_117, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.38/0.61  cnf(c_0_118, negated_conjecture, (v5_pre_topc(esk4_0,X1,esk3_0)|~v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk3_0)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(esk3_0))|~v1_funct_2(esk4_0,u1_struct_0(X1),u1_struct_0(esk3_0))|~v4_relat_1(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_60]), c_0_28]), c_0_29]), c_0_31])])).
% 0.38/0.61  cnf(c_0_119, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_27]), c_0_45]), c_0_46]), c_0_30]), c_0_31])])).
% 0.38/0.61  cnf(c_0_120, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_partfun1(esk4_0,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_111]), c_0_112])])).
% 0.38/0.61  cnf(c_0_121, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v1_partfun1(esk4_0,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_111]), c_0_112])])).
% 0.38/0.61  cnf(c_0_122, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_45]), c_0_46]), c_0_78]), c_0_31]), c_0_39])]), c_0_116])).
% 0.38/0.61  cnf(c_0_123, negated_conjecture, (~r2_hidden(X1,esk4_0)|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))), inference(spm,[status(thm)],[c_0_117, c_0_27])).
% 0.38/0.61  cnf(c_0_124, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.38/0.61  cnf(c_0_125, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_70]), c_0_45]), c_0_46]), c_0_78]), c_0_39])])).
% 0.38/0.61  cnf(c_0_126, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(spm,[status(thm)],[c_0_119, c_0_36])).
% 0.38/0.61  cnf(c_0_127, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_partfun1(esk4_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 0.38/0.61  cnf(c_0_128, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_44]), c_0_28]), c_0_29])])).
% 0.38/0.61  cnf(c_0_129, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))!=k1_xboole_0|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_101]), c_0_124])])).
% 0.38/0.61  cnf(c_0_130, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_75]), c_0_85]), c_0_106])).
% 0.38/0.61  fof(c_0_131, plain, ![X33, X35, X36, X37]:((r2_hidden(esk1_1(X33),X33)|X33=k1_xboole_0)&((~r2_hidden(X35,X33)|esk1_1(X33)!=k3_mcart_1(X35,X36,X37)|X33=k1_xboole_0)&(~r2_hidden(X36,X33)|esk1_1(X33)!=k3_mcart_1(X35,X36,X37)|X33=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.38/0.61  cnf(c_0_132, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|v5_pre_topc(esk4_0,esk2_0,esk3_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_44]), c_0_28]), c_0_29])])).
% 0.38/0.61  cnf(c_0_133, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_partfun1(esk4_0,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_44]), c_0_28]), c_0_29])])).
% 0.38/0.61  cnf(c_0_134, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),k1_xboole_0)|~m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_128, c_0_57])).
% 0.38/0.61  cnf(c_0_135, negated_conjecture, (~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_130])])).
% 0.38/0.61  cnf(c_0_136, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_131])).
% 0.38/0.61  cnf(c_0_137, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))|~m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_132, c_0_57])).
% 0.38/0.61  cnf(c_0_138, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v1_partfun1(esk4_0,u1_struct_0(esk2_0))|~m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_133, c_0_57])).
% 0.38/0.61  fof(c_0_139, plain, ![X8]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.38/0.61  cnf(c_0_140, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,X1)|~v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(X1))|~v5_relat_1(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X1))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_98]), c_0_45]), c_0_46]), c_0_31])])).
% 0.38/0.61  cnf(c_0_141, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_67]), c_0_29])])).
% 0.38/0.61  cnf(c_0_142, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 0.38/0.61  cnf(c_0_143, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_67]), c_0_29])])).
% 0.38/0.61  cnf(c_0_144, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v1_partfun1(esk4_0,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_67]), c_0_29])])).
% 0.38/0.61  cnf(c_0_145, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_139])).
% 0.38/0.61  cnf(c_0_146, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_97]), c_0_28]), c_0_29]), c_0_78]), c_0_39])])).
% 0.38/0.61  cnf(c_0_147, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk2_0,esk3_0)|~v1_funct_2(k1_xboole_0,u1_struct_0(esk2_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_141, c_0_142]), c_0_142])).
% 0.38/0.61  cnf(c_0_148, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v1_partfun1(esk4_0,u1_struct_0(esk2_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_111]), c_0_112])])).
% 0.38/0.61  cnf(c_0_149, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk2_0,esk3_0)|~v1_partfun1(k1_xboole_0,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_144, c_0_142]), c_0_142])).
% 0.38/0.61  cnf(c_0_150, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_62, c_0_145])).
% 0.38/0.61  cnf(c_0_151, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v1_partfun1(esk4_0,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_39]), c_0_78]), c_0_31])])).
% 0.38/0.61  cnf(c_0_152, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(esk2_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_146, c_0_130]), c_0_142]), c_0_142]), c_0_142]), c_0_147])).
% 0.38/0.61  cnf(c_0_153, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_partfun1(k1_xboole_0,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_148, c_0_130]), c_0_142]), c_0_142]), c_0_142]), c_0_142]), c_0_145])]), c_0_149])).
% 0.38/0.61  cnf(c_0_154, negated_conjecture, (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|~v1_partfun1(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_130]), c_0_142]), c_0_142]), c_0_142]), c_0_150])])).
% 0.38/0.61  cnf(c_0_155, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v1_partfun1(k1_xboole_0,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_151, c_0_142])).
% 0.38/0.61  cnf(c_0_156, negated_conjecture, (~v1_partfun1(k1_xboole_0,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_154])).
% 0.38/0.61  cnf(c_0_157, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_155, c_0_156])).
% 0.38/0.61  cnf(c_0_158, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_78, c_0_142])).
% 0.38/0.61  cnf(c_0_159, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk2_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(esk2_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_152, c_0_157])).
% 0.38/0.61  cnf(c_0_160, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(esk2_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_158, c_0_157])).
% 0.38/0.61  cnf(c_0_161, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk2_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_159, c_0_160])])).
% 0.38/0.61  cnf(c_0_162, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_147, c_0_160])])).
% 0.38/0.61  cnf(c_0_163, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_143, c_0_130]), c_0_130]), c_0_142]), c_0_157]), c_0_142]), c_0_142]), c_0_160]), c_0_142]), c_0_145])]), c_0_161]), c_0_162]), ['proof']).
% 0.38/0.61  # SZS output end CNFRefutation
% 0.38/0.61  # Proof object total steps             : 164
% 0.38/0.61  # Proof object clause steps            : 126
% 0.38/0.61  # Proof object formula steps           : 38
% 0.38/0.61  # Proof object conjectures             : 101
% 0.38/0.61  # Proof object clause conjectures      : 98
% 0.38/0.61  # Proof object formula conjectures     : 3
% 0.38/0.61  # Proof object initial clauses used    : 33
% 0.38/0.61  # Proof object initial formulas used   : 19
% 0.38/0.61  # Proof object generating inferences   : 70
% 0.38/0.61  # Proof object simplifying inferences  : 182
% 0.38/0.61  # Training examples: 0 positive, 0 negative
% 0.38/0.61  # Parsed axioms                        : 20
% 0.38/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.61  # Initial clauses                      : 45
% 0.38/0.61  # Removed in clause preprocessing      : 1
% 0.38/0.61  # Initial clauses in saturation        : 44
% 0.38/0.61  # Processed clauses                    : 905
% 0.38/0.61  # ...of these trivial                  : 15
% 0.38/0.61  # ...subsumed                          : 400
% 0.38/0.61  # ...remaining for further processing  : 489
% 0.38/0.61  # Other redundant clauses eliminated   : 6
% 0.38/0.61  # Clauses deleted for lack of memory   : 0
% 0.38/0.61  # Backward-subsumed                    : 62
% 0.38/0.61  # Backward-rewritten                   : 260
% 0.38/0.61  # Generated clauses                    : 2112
% 0.38/0.61  # ...of the previous two non-trivial   : 1987
% 0.38/0.61  # Contextual simplify-reflections      : 48
% 0.38/0.61  # Paramodulations                      : 2097
% 0.38/0.61  # Factorizations                       : 8
% 0.38/0.61  # Equation resolutions                 : 6
% 0.38/0.61  # Propositional unsat checks           : 0
% 0.38/0.61  #    Propositional check models        : 0
% 0.38/0.61  #    Propositional check unsatisfiable : 0
% 0.38/0.61  #    Propositional clauses             : 0
% 0.38/0.61  #    Propositional clauses after purity: 0
% 0.38/0.61  #    Propositional unsat core size     : 0
% 0.38/0.61  #    Propositional preprocessing time  : 0.000
% 0.38/0.61  #    Propositional encoding time       : 0.000
% 0.38/0.61  #    Propositional solver time         : 0.000
% 0.38/0.61  #    Success case prop preproc time    : 0.000
% 0.38/0.61  #    Success case prop encoding time   : 0.000
% 0.38/0.61  #    Success case prop solver time     : 0.000
% 0.38/0.61  # Current number of processed clauses  : 162
% 0.38/0.61  #    Positive orientable unit clauses  : 19
% 0.38/0.61  #    Positive unorientable unit clauses: 0
% 0.38/0.61  #    Negative unit clauses             : 5
% 0.38/0.61  #    Non-unit-clauses                  : 138
% 0.38/0.61  # Current number of unprocessed clauses: 986
% 0.38/0.61  # ...number of literals in the above   : 7068
% 0.38/0.61  # Current number of archived formulas  : 0
% 0.38/0.61  # Current number of archived clauses   : 323
% 0.38/0.61  # Clause-clause subsumption calls (NU) : 68369
% 0.38/0.61  # Rec. Clause-clause subsumption calls : 8245
% 0.38/0.61  # Non-unit clause-clause subsumptions  : 427
% 0.38/0.61  # Unit Clause-clause subsumption calls : 606
% 0.38/0.61  # Rewrite failures with RHS unbound    : 0
% 0.38/0.61  # BW rewrite match attempts            : 14
% 0.38/0.61  # BW rewrite match successes           : 8
% 0.38/0.61  # Condensation attempts                : 0
% 0.38/0.61  # Condensation successes               : 0
% 0.38/0.61  # Termbank termtop insertions          : 317631
% 0.38/0.61  
% 0.38/0.61  # -------------------------------------------------
% 0.38/0.61  # User time                : 0.260 s
% 0.38/0.61  # System time              : 0.008 s
% 0.38/0.61  # Total time               : 0.268 s
% 0.38/0.61  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
