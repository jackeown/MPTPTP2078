%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:24 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  162 (2488 expanded)
%              Number of clauses        :  120 ( 923 expanded)
%              Number of leaves         :   21 ( 599 expanded)
%              Depth                    :   22
%              Number of atoms          :  660 (21060 expanded)
%              Number of equality atoms :  121 (1885 expanded)
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

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

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

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d1_funct_1,axiom,(
    ! [X1] :
      ( v1_funct_1(X1)
    <=> ! [X2,X3,X4] :
          ( ( r2_hidden(k4_tarski(X2,X3),X1)
            & r2_hidden(k4_tarski(X2,X4),X1) )
         => X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_23,plain,(
    ! [X34,X35,X36] :
      ( ( v4_relat_1(X36,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( v5_relat_1(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( esk8_0 = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | v1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_27,plain,(
    ! [X52,X53] :
      ( ( ~ v1_partfun1(X53,X52)
        | k1_relat_1(X53) = X52
        | ~ v1_relat_1(X53)
        | ~ v4_relat_1(X53,X52) )
      & ( k1_relat_1(X53) != X52
        | v1_partfun1(X53,X52)
        | ~ v1_relat_1(X53)
        | ~ v4_relat_1(X53,X52) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_28,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X43,X44,X45] :
      ( ( v1_funct_1(X45)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | v1_xboole_0(X44) )
      & ( v1_partfun1(X45,X43)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | v1_xboole_0(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(esk9_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_33,plain,(
    ! [X62,X63,X64,X65] :
      ( ( ~ v5_pre_topc(X64,X62,X63)
        | v5_pre_topc(X65,X62,g1_pre_topc(u1_struct_0(X63),u1_pre_topc(X63)))
        | X64 != X65
        | ~ v1_funct_1(X65)
        | ~ v1_funct_2(X65,u1_struct_0(X62),u1_struct_0(g1_pre_topc(u1_struct_0(X63),u1_pre_topc(X63))))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(g1_pre_topc(u1_struct_0(X63),u1_pre_topc(X63))))))
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,u1_struct_0(X62),u1_struct_0(X63))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(X63))))
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62) )
      & ( ~ v5_pre_topc(X65,X62,g1_pre_topc(u1_struct_0(X63),u1_pre_topc(X63)))
        | v5_pre_topc(X64,X62,X63)
        | X64 != X65
        | ~ v1_funct_1(X65)
        | ~ v1_funct_2(X65,u1_struct_0(X62),u1_struct_0(g1_pre_topc(u1_struct_0(X63),u1_pre_topc(X63))))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(g1_pre_topc(u1_struct_0(X63),u1_pre_topc(X63))))))
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,u1_struct_0(X62),u1_struct_0(X63))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(X63))))
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_35,plain,(
    ! [X12,X13] :
      ( ~ v1_xboole_0(X12)
      | X12 = X13
      | ~ v1_xboole_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_36,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( v4_relat_1(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_39,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ v5_pre_topc(esk9_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_44,plain,(
    ! [X58,X59,X60,X61] :
      ( ( ~ v5_pre_topc(X60,X58,X59)
        | v5_pre_topc(X61,g1_pre_topc(u1_struct_0(X58),u1_pre_topc(X58)),X59)
        | X60 != X61
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,u1_struct_0(g1_pre_topc(u1_struct_0(X58),u1_pre_topc(X58))),u1_struct_0(X59))
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X58),u1_pre_topc(X58))),u1_struct_0(X59))))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,u1_struct_0(X58),u1_struct_0(X59))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X59))))
        | ~ v2_pre_topc(X59)
        | ~ l1_pre_topc(X59)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58) )
      & ( ~ v5_pre_topc(X61,g1_pre_topc(u1_struct_0(X58),u1_pre_topc(X58)),X59)
        | v5_pre_topc(X60,X58,X59)
        | X60 != X61
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,u1_struct_0(g1_pre_topc(u1_struct_0(X58),u1_pre_topc(X58))),u1_struct_0(X59))
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X58),u1_pre_topc(X58))),u1_struct_0(X59))))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,u1_struct_0(X58),u1_struct_0(X59))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X59))))
        | ~ v2_pre_topc(X59)
        | ~ l1_pre_topc(X59)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).

fof(c_0_45,plain,(
    ! [X20,X21,X22] :
      ( ~ r2_hidden(X20,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X22))
      | ~ v1_xboole_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_46,negated_conjecture,
    ( v4_relat_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(esk8_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v1_partfun1(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_51,negated_conjecture,
    ( v1_partfun1(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_29]),c_0_40]),c_0_41])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v5_pre_topc(esk8_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_25])).

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
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_56,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_58,plain,(
    ! [X14,X15] :
      ( ( k2_zfmisc_1(X14,X15) != k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_59,negated_conjecture,
    ( k1_relat_1(esk8_0) = u1_struct_0(esk6_0)
    | ~ v1_partfun1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_46]),c_0_38])])).

cnf(c_0_60,negated_conjecture,
    ( v1_partfun1(esk8_0,u1_struct_0(esk6_0))
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_34]),c_0_47]),c_0_41])])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_62,negated_conjecture,
    ( k1_relat_1(esk8_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_63,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k1_relset_1(X37,X38,X39) = k1_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_64,plain,(
    ! [X49,X50,X51] :
      ( ( ~ v1_funct_2(X51,X49,X50)
        | X49 = k1_relset_1(X49,X50,X51)
        | X50 = k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( X49 != k1_relset_1(X49,X50,X51)
        | v1_funct_2(X51,X49,X50)
        | X50 = k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( ~ v1_funct_2(X51,X49,X50)
        | X49 = k1_relset_1(X49,X50,X51)
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( X49 != k1_relset_1(X49,X50,X51)
        | v1_funct_2(X51,X49,X50)
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( ~ v1_funct_2(X51,X49,X50)
        | X51 = k1_xboole_0
        | X49 = k1_xboole_0
        | X50 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( X51 != k1_xboole_0
        | v1_funct_2(X51,X49,X50)
        | X49 = k1_xboole_0
        | X50 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_65,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_66,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | v5_pre_topc(esk9_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_67,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),esk7_0)
    | ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55]),c_0_40]),c_0_41]),c_0_29])])).

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
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_70,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_29])).

cnf(c_0_72,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_73,negated_conjecture,
    ( k1_relat_1(esk8_0) = u1_struct_0(esk6_0)
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( k1_relat_1(esk8_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_75,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_76,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

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
    inference(split_conjunct,[status(thm)],[c_0_44])).

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
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_79,negated_conjecture,
    ( v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | v5_pre_topc(esk8_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_66,c_0_25])).

cnf(c_0_80,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_54]),c_0_69]),c_0_55]),c_0_70]),c_0_47]),c_0_41]),c_0_34])])).

cnf(c_0_81,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) != k1_xboole_0
    | ~ r2_hidden(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_49])])).

cnf(c_0_82,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))) = u1_struct_0(esk6_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

fof(c_0_83,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_84,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( ~ v1_funct_1(X23)
        | ~ r2_hidden(k4_tarski(X24,X25),X23)
        | ~ r2_hidden(k4_tarski(X24,X26),X23)
        | X25 = X26 )
      & ( r2_hidden(k4_tarski(esk3_1(X27),esk4_1(X27)),X27)
        | v1_funct_1(X27) )
      & ( r2_hidden(k4_tarski(esk3_1(X27),esk5_1(X27)),X27)
        | v1_funct_1(X27) )
      & ( esk4_1(X27) != esk5_1(X27)
        | v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_1])])])])])])).

fof(c_0_85,plain,(
    ! [X16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_86,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_68]),c_0_69]),c_0_70]),c_0_40]),c_0_41]),c_0_29])])).

cnf(c_0_87,plain,
    ( X1 = k1_relat_1(X2)
    | X1 != k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

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
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_89,negated_conjecture,
    ( v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),esk7_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_54]),c_0_55]),c_0_40]),c_0_41]),c_0_29])]),c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))) = u1_struct_0(esk6_0)
    | v1_xboole_0(u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_91,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_92,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_93,plain,
    ( r2_hidden(k4_tarski(esk3_1(X1),esk4_1(X1)),X1)
    | v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_94,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,esk6_0,esk7_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_53]),c_0_54]),c_0_69]),c_0_55]),c_0_70]),c_0_47]),c_0_41]),c_0_34])])).

cnf(c_0_96,negated_conjecture,
    ( k1_relat_1(esk8_0) = u1_struct_0(esk6_0)
    | u1_struct_0(esk6_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_34]),c_0_47])])).

cnf(c_0_97,negated_conjecture,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_54]),c_0_69]),c_0_55]),c_0_70]),c_0_47]),c_0_41]),c_0_34])]),c_0_80])).

cnf(c_0_98,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))) = u1_struct_0(esk6_0)
    | v1_xboole_0(u1_struct_0(esk7_0))
    | v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

fof(c_0_99,plain,(
    ! [X57] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X57),u1_pre_topc(X57)))
        | ~ v2_pre_topc(X57)
        | ~ l1_pre_topc(X57) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X57),u1_pre_topc(X57)))
        | ~ v2_pre_topc(X57)
        | ~ l1_pre_topc(X57) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

fof(c_0_100,plain,(
    ! [X46,X47,X48] :
      ( ( v1_funct_1(X48)
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
        | v1_xboole_0(X46)
        | v1_xboole_0(X47) )
      & ( ~ v1_xboole_0(X48)
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
        | v1_xboole_0(X46)
        | v1_xboole_0(X47) )
      & ( v1_funct_2(X48,X46,X47)
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
        | v1_xboole_0(X46)
        | v1_xboole_0(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).

fof(c_0_101,plain,(
    ! [X40,X41,X42] :
      ( ( v1_funct_1(X42)
        | ~ v1_funct_1(X42)
        | ~ v1_partfun1(X42,X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( v1_funct_2(X42,X40,X41)
        | ~ v1_funct_1(X42)
        | ~ v1_partfun1(X42,X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_102,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_103,plain,
    ( v1_partfun1(X1,X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_104,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_94])).

cnf(c_0_105,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_94])).

cnf(c_0_106,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_79]),c_0_69]),c_0_70]),c_0_40]),c_0_41]),c_0_29])]),c_0_95])).

cnf(c_0_107,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_108,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_109,negated_conjecture,
    ( k1_relset_1(X1,X2,esk8_0) = u1_struct_0(esk6_0)
    | u1_struct_0(esk6_0) != k1_xboole_0
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_96])).

cnf(c_0_110,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v1_xboole_0(esk8_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_47]),c_0_34])])).

cnf(c_0_111,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

fof(c_0_112,plain,(
    ! [X54,X55] :
      ( ( v1_pre_topc(g1_pre_topc(X54,X55))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k1_zfmisc_1(X54))) )
      & ( l1_pre_topc(g1_pre_topc(X54,X55))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k1_zfmisc_1(X54))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_113,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_114,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_115,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_49])).

cnf(c_0_116,plain,
    ( v1_partfun1(k1_xboole_0,X1)
    | k1_relat_1(k1_xboole_0) != X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105])])).

cnf(c_0_117,negated_conjecture,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_106]),c_0_54]),c_0_69]),c_0_55]),c_0_70]),c_0_47]),c_0_41]),c_0_34])]),c_0_95])).

cnf(c_0_118,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(esk6_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_107])).

cnf(c_0_119,negated_conjecture,
    ( v1_funct_2(esk8_0,X1,X2)
    | u1_struct_0(esk6_0) != k1_xboole_0
    | u1_struct_0(esk6_0) != X1
    | X1 != k1_xboole_0
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_120,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v1_xboole_0(esk8_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_69]),c_0_70])])).

cnf(c_0_121,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

fof(c_0_122,plain,(
    ! [X56] :
      ( ~ l1_pre_topc(X56)
      | m1_subset_1(u1_pre_topc(X56),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X56)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_123,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_34])).

cnf(c_0_124,plain,
    ( v1_xboole_0(X1)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(ef,[status(thm)],[c_0_113]),c_0_102])).

cnf(c_0_125,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | ~ v1_partfun1(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_94]),c_0_115])])).

cnf(c_0_126,plain,
    ( v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_116])).

cnf(c_0_127,negated_conjecture,
    ( u1_struct_0(esk6_0) != k1_xboole_0
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_107]),c_0_118])).

cnf(c_0_128,negated_conjecture,
    ( v1_funct_2(esk8_0,X1,X2)
    | u1_struct_0(esk6_0) != k1_xboole_0
    | u1_struct_0(esk6_0) != X1
    | X1 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_107]),c_0_118])).

cnf(c_0_129,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_130,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v1_xboole_0(esk8_0)
    | ~ m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_131,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_122])).

cnf(c_0_132,negated_conjecture,
    ( u1_struct_0(esk7_0) != k1_xboole_0
    | ~ r2_hidden(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_72]),c_0_49])])).

cnf(c_0_133,plain,
    ( v1_xboole_0(X1)
    | ~ v1_funct_2(k1_xboole_0,X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_94]),c_0_49])])).

cnf(c_0_134,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_135,negated_conjecture,
    ( u1_struct_0(esk6_0) != k1_xboole_0
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_136,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0),esk8_0) = u1_struct_0(esk6_0)
    | u1_struct_0(esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_34]),c_0_47])])).

cnf(c_0_137,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_70])])).

cnf(c_0_138,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | u1_struct_0(esk7_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_132,c_0_91])).

cnf(c_0_139,plain,
    ( k1_relat_1(k1_xboole_0) = X1
    | ~ v1_partfun1(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_104]),c_0_105])])).

cnf(c_0_140,plain,
    ( v1_partfun1(k1_xboole_0,k1_relset_1(X1,X2,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_75]),c_0_94])])).

cnf(c_0_141,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_142,negated_conjecture,
    ( u1_struct_0(esk6_0) != k1_xboole_0
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_111]),c_0_54]),c_0_55])])).

cnf(c_0_143,negated_conjecture,
    ( k1_relat_1(esk8_0) = u1_struct_0(esk6_0)
    | u1_struct_0(esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_136]),c_0_34])])).

cnf(c_0_144,negated_conjecture,
    ( v1_xboole_0(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_137]),c_0_138])).

cnf(c_0_145,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(X1,X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_146,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_141])).

cnf(c_0_147,negated_conjecture,
    ( u1_struct_0(esk6_0) != k1_xboole_0
    | ~ m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_142,c_0_121])).

cnf(c_0_148,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_149,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relat_1(X1) != X2
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_75])).

cnf(c_0_150,negated_conjecture,
    ( k1_relset_1(X1,X2,esk8_0) = u1_struct_0(esk6_0)
    | u1_struct_0(esk7_0) = k1_xboole_0
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_143])).

cnf(c_0_151,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_144])).

cnf(c_0_152,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_145,c_0_146])).

cnf(c_0_153,negated_conjecture,
    ( u1_struct_0(esk6_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_131]),c_0_55])])).

cnf(c_0_154,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,X2)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_148,c_0_94])).

cnf(c_0_155,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | k1_xboole_0 != X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_94]),c_0_146])])).

cnf(c_0_156,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_150,c_0_151]),c_0_152]),c_0_151]),c_0_94])]),c_0_153])).

cnf(c_0_157,plain,
    ( v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_154]),c_0_155])).

cnf(c_0_158,negated_conjecture,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_151]),c_0_151]),c_0_94])]),c_0_156]),c_0_157])])).

cnf(c_0_159,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_111]),c_0_69]),c_0_70])])).

cnf(c_0_160,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_159,c_0_121])).

cnf(c_0_161,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_131]),c_0_70])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.49  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.19/0.49  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.49  #
% 0.19/0.49  # Preprocessing time       : 0.044 s
% 0.19/0.49  
% 0.19/0.49  # Proof found!
% 0.19/0.49  # SZS status Theorem
% 0.19/0.49  # SZS output start CNFRefutation
% 0.19/0.49  fof(t64_pre_topc, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_pre_topc)).
% 0.19/0.49  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.49  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.49  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.19/0.49  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.19/0.49  fof(t63_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_pre_topc)).
% 0.19/0.49  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.19/0.49  fof(t62_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 0.19/0.49  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.49  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.49  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.49  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.49  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.49  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.49  fof(d1_funct_1, axiom, ![X1]:(v1_funct_1(X1)<=>![X2, X3, X4]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X2,X4),X1))=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_1)).
% 0.19/0.49  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.49  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.19/0.49  fof(cc6_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&~(v1_xboole_0(X3)))&v1_funct_2(X3,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 0.19/0.49  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.19/0.49  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.19/0.49  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.19/0.49  fof(c_0_21, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))))), inference(assume_negation,[status(cth)],[t64_pre_topc])).
% 0.19/0.49  fof(c_0_22, negated_conjecture, ((v2_pre_topc(esk6_0)&l1_pre_topc(esk6_0))&((v2_pre_topc(esk7_0)&l1_pre_topc(esk7_0))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)))))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))))&(esk8_0=esk9_0&((~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~v5_pre_topc(esk9_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))&(v5_pre_topc(esk8_0,esk6_0,esk7_0)|v5_pre_topc(esk9_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.19/0.49  fof(c_0_23, plain, ![X34, X35, X36]:((v4_relat_1(X36,X34)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(v5_relat_1(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.49  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  cnf(c_0_25, negated_conjecture, (esk8_0=esk9_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  fof(c_0_26, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|v1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.49  fof(c_0_27, plain, ![X52, X53]:((~v1_partfun1(X53,X52)|k1_relat_1(X53)=X52|(~v1_relat_1(X53)|~v4_relat_1(X53,X52)))&(k1_relat_1(X53)!=X52|v1_partfun1(X53,X52)|(~v1_relat_1(X53)|~v4_relat_1(X53,X52)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.19/0.49  cnf(c_0_28, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.49  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.49  cnf(c_0_30, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.49  fof(c_0_31, plain, ![X43, X44, X45]:((v1_funct_1(X45)|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X44))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|v1_xboole_0(X44))&(v1_partfun1(X45,X43)|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X44))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|v1_xboole_0(X44))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.19/0.49  cnf(c_0_32, negated_conjecture, (v1_funct_2(esk9_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  fof(c_0_33, plain, ![X62, X63, X64, X65]:((~v5_pre_topc(X64,X62,X63)|v5_pre_topc(X65,X62,g1_pre_topc(u1_struct_0(X63),u1_pre_topc(X63)))|X64!=X65|(~v1_funct_1(X65)|~v1_funct_2(X65,u1_struct_0(X62),u1_struct_0(g1_pre_topc(u1_struct_0(X63),u1_pre_topc(X63))))|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(g1_pre_topc(u1_struct_0(X63),u1_pre_topc(X63)))))))|(~v1_funct_1(X64)|~v1_funct_2(X64,u1_struct_0(X62),u1_struct_0(X63))|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(X63)))))|(~v2_pre_topc(X63)|~l1_pre_topc(X63))|(~v2_pre_topc(X62)|~l1_pre_topc(X62)))&(~v5_pre_topc(X65,X62,g1_pre_topc(u1_struct_0(X63),u1_pre_topc(X63)))|v5_pre_topc(X64,X62,X63)|X64!=X65|(~v1_funct_1(X65)|~v1_funct_2(X65,u1_struct_0(X62),u1_struct_0(g1_pre_topc(u1_struct_0(X63),u1_pre_topc(X63))))|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(g1_pre_topc(u1_struct_0(X63),u1_pre_topc(X63)))))))|(~v1_funct_1(X64)|~v1_funct_2(X64,u1_struct_0(X62),u1_struct_0(X63))|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(X63)))))|(~v2_pre_topc(X63)|~l1_pre_topc(X63))|(~v2_pre_topc(X62)|~l1_pre_topc(X62)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).
% 0.19/0.49  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  fof(c_0_35, plain, ![X12, X13]:(~v1_xboole_0(X12)|X12=X13|~v1_xboole_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.19/0.49  cnf(c_0_36, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.49  cnf(c_0_37, negated_conjecture, (v4_relat_1(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.49  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 0.19/0.49  cnf(c_0_39, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.49  cnf(c_0_40, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))), inference(rw,[status(thm)],[c_0_32, c_0_25])).
% 0.19/0.49  cnf(c_0_41, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  cnf(c_0_42, negated_conjecture, (~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~v5_pre_topc(esk9_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  cnf(c_0_43, plain, (v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.49  fof(c_0_44, plain, ![X58, X59, X60, X61]:((~v5_pre_topc(X60,X58,X59)|v5_pre_topc(X61,g1_pre_topc(u1_struct_0(X58),u1_pre_topc(X58)),X59)|X60!=X61|(~v1_funct_1(X61)|~v1_funct_2(X61,u1_struct_0(g1_pre_topc(u1_struct_0(X58),u1_pre_topc(X58))),u1_struct_0(X59))|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X58),u1_pre_topc(X58))),u1_struct_0(X59)))))|(~v1_funct_1(X60)|~v1_funct_2(X60,u1_struct_0(X58),u1_struct_0(X59))|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X59)))))|(~v2_pre_topc(X59)|~l1_pre_topc(X59))|(~v2_pre_topc(X58)|~l1_pre_topc(X58)))&(~v5_pre_topc(X61,g1_pre_topc(u1_struct_0(X58),u1_pre_topc(X58)),X59)|v5_pre_topc(X60,X58,X59)|X60!=X61|(~v1_funct_1(X61)|~v1_funct_2(X61,u1_struct_0(g1_pre_topc(u1_struct_0(X58),u1_pre_topc(X58))),u1_struct_0(X59))|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X58),u1_pre_topc(X58))),u1_struct_0(X59)))))|(~v1_funct_1(X60)|~v1_funct_2(X60,u1_struct_0(X58),u1_struct_0(X59))|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X59)))))|(~v2_pre_topc(X59)|~l1_pre_topc(X59))|(~v2_pre_topc(X58)|~l1_pre_topc(X58)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).
% 0.19/0.49  fof(c_0_45, plain, ![X20, X21, X22]:(~r2_hidden(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(X22))|~v1_xboole_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.49  cnf(c_0_46, negated_conjecture, (v4_relat_1(esk8_0,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_34])).
% 0.19/0.49  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  cnf(c_0_48, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.49  cnf(c_0_49, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.49  cnf(c_0_50, negated_conjecture, (k1_relat_1(esk8_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v1_partfun1(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.19/0.49  cnf(c_0_51, negated_conjecture, (v1_partfun1(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))))|v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_29]), c_0_40]), c_0_41])])).
% 0.19/0.49  cnf(c_0_52, negated_conjecture, (~v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v5_pre_topc(esk8_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_42, c_0_25])).
% 0.19/0.49  cnf(c_0_53, plain, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_43])).
% 0.19/0.49  cnf(c_0_54, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  cnf(c_0_55, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  cnf(c_0_56, plain, (v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.49  cnf(c_0_57, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.49  fof(c_0_58, plain, ![X14, X15]:((k2_zfmisc_1(X14,X15)!=k1_xboole_0|(X14=k1_xboole_0|X15=k1_xboole_0))&((X14!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0)&(X15!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.49  cnf(c_0_59, negated_conjecture, (k1_relat_1(esk8_0)=u1_struct_0(esk6_0)|~v1_partfun1(esk8_0,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_46]), c_0_38])])).
% 0.19/0.49  cnf(c_0_60, negated_conjecture, (v1_partfun1(esk8_0,u1_struct_0(esk6_0))|v1_xboole_0(u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_34]), c_0_47]), c_0_41])])).
% 0.19/0.49  cnf(c_0_61, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.49  cnf(c_0_62, negated_conjecture, (k1_relat_1(esk8_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.49  fof(c_0_63, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k1_relset_1(X37,X38,X39)=k1_relat_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.49  fof(c_0_64, plain, ![X49, X50, X51]:((((~v1_funct_2(X51,X49,X50)|X49=k1_relset_1(X49,X50,X51)|X50=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))&(X49!=k1_relset_1(X49,X50,X51)|v1_funct_2(X51,X49,X50)|X50=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))&((~v1_funct_2(X51,X49,X50)|X49=k1_relset_1(X49,X50,X51)|X49!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))&(X49!=k1_relset_1(X49,X50,X51)|v1_funct_2(X51,X49,X50)|X49!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))))&((~v1_funct_2(X51,X49,X50)|X51=k1_xboole_0|X49=k1_xboole_0|X50!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))&(X51!=k1_xboole_0|v1_funct_2(X51,X49,X50)|X49=k1_xboole_0|X50!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.49  cnf(c_0_65, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.49  cnf(c_0_66, negated_conjecture, (v5_pre_topc(esk8_0,esk6_0,esk7_0)|v5_pre_topc(esk9_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  cnf(c_0_67, negated_conjecture, (~v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),esk7_0)|~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55]), c_0_40]), c_0_41]), c_0_29])])).
% 0.19/0.49  cnf(c_0_68, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_56])).
% 0.19/0.49  cnf(c_0_69, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  cnf(c_0_70, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  cnf(c_0_71, negated_conjecture, (~r2_hidden(X1,esk8_0)|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))))), inference(spm,[status(thm)],[c_0_57, c_0_29])).
% 0.19/0.49  cnf(c_0_72, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.49  cnf(c_0_73, negated_conjecture, (k1_relat_1(esk8_0)=u1_struct_0(esk6_0)|v1_xboole_0(u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.49  cnf(c_0_74, negated_conjecture, (k1_relat_1(esk8_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.49  cnf(c_0_75, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.49  cnf(c_0_76, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.49  cnf(c_0_77, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.49  cnf(c_0_78, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_65])).
% 0.19/0.49  cnf(c_0_79, negated_conjecture, (v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|v5_pre_topc(esk8_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_66, c_0_25])).
% 0.19/0.49  cnf(c_0_80, negated_conjecture, (~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_54]), c_0_69]), c_0_55]), c_0_70]), c_0_47]), c_0_41]), c_0_34])])).
% 0.19/0.49  cnf(c_0_81, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))!=k1_xboole_0|~r2_hidden(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_49])])).
% 0.19/0.49  cnf(c_0_82, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))=u1_struct_0(esk6_0)|u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))=k1_xboole_0|v1_xboole_0(u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.49  fof(c_0_83, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.49  fof(c_0_84, plain, ![X23, X24, X25, X26, X27]:((~v1_funct_1(X23)|(~r2_hidden(k4_tarski(X24,X25),X23)|~r2_hidden(k4_tarski(X24,X26),X23)|X25=X26))&(((r2_hidden(k4_tarski(esk3_1(X27),esk4_1(X27)),X27)|v1_funct_1(X27))&(r2_hidden(k4_tarski(esk3_1(X27),esk5_1(X27)),X27)|v1_funct_1(X27)))&(esk4_1(X27)!=esk5_1(X27)|v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_1])])])])])])).
% 0.19/0.49  fof(c_0_85, plain, ![X16]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.49  cnf(c_0_86, negated_conjecture, (~v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_68]), c_0_69]), c_0_70]), c_0_40]), c_0_41]), c_0_29])])).
% 0.19/0.49  cnf(c_0_87, plain, (X1=k1_relat_1(X2)|X1!=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.49  cnf(c_0_88, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_77])).
% 0.19/0.49  cnf(c_0_89, negated_conjecture, (v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)),esk7_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_54]), c_0_55]), c_0_40]), c_0_41]), c_0_29])]), c_0_80])).
% 0.19/0.49  cnf(c_0_90, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))=u1_struct_0(esk6_0)|v1_xboole_0(u1_struct_0(esk7_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.49  cnf(c_0_91, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.19/0.49  cnf(c_0_92, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.19/0.49  cnf(c_0_93, plain, (r2_hidden(k4_tarski(esk3_1(X1),esk4_1(X1)),X1)|v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.19/0.49  cnf(c_0_94, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.19/0.49  cnf(c_0_95, negated_conjecture, (~v5_pre_topc(esk8_0,esk6_0,esk7_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_53]), c_0_54]), c_0_69]), c_0_55]), c_0_70]), c_0_47]), c_0_41]), c_0_34])])).
% 0.19/0.49  cnf(c_0_96, negated_conjecture, (k1_relat_1(esk8_0)=u1_struct_0(esk6_0)|u1_struct_0(esk6_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_34]), c_0_47])])).
% 0.19/0.49  cnf(c_0_97, negated_conjecture, (~v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))),u1_struct_0(esk7_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_54]), c_0_69]), c_0_55]), c_0_70]), c_0_47]), c_0_41]), c_0_34])]), c_0_80])).
% 0.19/0.49  cnf(c_0_98, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))=u1_struct_0(esk6_0)|v1_xboole_0(u1_struct_0(esk7_0))|v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.19/0.49  fof(c_0_99, plain, ![X57]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X57),u1_pre_topc(X57)))|(~v2_pre_topc(X57)|~l1_pre_topc(X57)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X57),u1_pre_topc(X57)))|(~v2_pre_topc(X57)|~l1_pre_topc(X57)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.19/0.49  fof(c_0_100, plain, ![X46, X47, X48]:(((v1_funct_1(X48)|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X47))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|(v1_xboole_0(X46)|v1_xboole_0(X47)))&(~v1_xboole_0(X48)|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X47))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|(v1_xboole_0(X46)|v1_xboole_0(X47))))&(v1_funct_2(X48,X46,X47)|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X47))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|(v1_xboole_0(X46)|v1_xboole_0(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).
% 0.19/0.49  fof(c_0_101, plain, ![X40, X41, X42]:((v1_funct_1(X42)|(~v1_funct_1(X42)|~v1_partfun1(X42,X40))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(v1_funct_2(X42,X40,X41)|(~v1_funct_1(X42)|~v1_partfun1(X42,X40))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.19/0.49  cnf(c_0_102, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.19/0.49  cnf(c_0_103, plain, (v1_partfun1(X1,X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.49  cnf(c_0_104, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_94])).
% 0.19/0.49  cnf(c_0_105, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_94])).
% 0.19/0.49  cnf(c_0_106, negated_conjecture, (v5_pre_topc(esk8_0,esk6_0,g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_79]), c_0_69]), c_0_70]), c_0_40]), c_0_41]), c_0_29])]), c_0_95])).
% 0.19/0.49  cnf(c_0_107, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.49  cnf(c_0_108, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.49  cnf(c_0_109, negated_conjecture, (k1_relset_1(X1,X2,esk8_0)=u1_struct_0(esk6_0)|u1_struct_0(esk6_0)!=k1_xboole_0|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_75, c_0_96])).
% 0.19/0.49  cnf(c_0_110, negated_conjecture, (v1_xboole_0(u1_struct_0(esk7_0))|v1_xboole_0(esk8_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_47]), c_0_34])])).
% 0.19/0.49  cnf(c_0_111, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.19/0.49  fof(c_0_112, plain, ![X54, X55]:((v1_pre_topc(g1_pre_topc(X54,X55))|~m1_subset_1(X55,k1_zfmisc_1(k1_zfmisc_1(X54))))&(l1_pre_topc(g1_pre_topc(X54,X55))|~m1_subset_1(X55,k1_zfmisc_1(k1_zfmisc_1(X54))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.19/0.49  cnf(c_0_113, plain, (v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.19/0.49  cnf(c_0_114, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.19/0.49  cnf(c_0_115, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_102, c_0_49])).
% 0.19/0.49  cnf(c_0_116, plain, (v1_partfun1(k1_xboole_0,X1)|k1_relat_1(k1_xboole_0)!=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_105])])).
% 0.19/0.49  cnf(c_0_117, negated_conjecture, (~v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_106]), c_0_54]), c_0_69]), c_0_55]), c_0_70]), c_0_47]), c_0_41]), c_0_34])]), c_0_95])).
% 0.19/0.49  cnf(c_0_118, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0))|u1_struct_0(esk6_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_107])).
% 0.19/0.49  cnf(c_0_119, negated_conjecture, (v1_funct_2(esk8_0,X1,X2)|u1_struct_0(esk6_0)!=k1_xboole_0|u1_struct_0(esk6_0)!=X1|X1!=k1_xboole_0|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.19/0.49  cnf(c_0_120, negated_conjecture, (v1_xboole_0(u1_struct_0(esk7_0))|v1_xboole_0(esk8_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_69]), c_0_70])])).
% 0.19/0.49  cnf(c_0_121, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_112])).
% 0.19/0.49  fof(c_0_122, plain, ![X56]:(~l1_pre_topc(X56)|m1_subset_1(u1_pre_topc(X56),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X56))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.19/0.49  cnf(c_0_123, negated_conjecture, (~r2_hidden(X1,esk8_0)|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_57, c_0_34])).
% 0.19/0.49  cnf(c_0_124, plain, (v1_xboole_0(X1)|~v1_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(ef,[status(thm)],[c_0_113]), c_0_102])).
% 0.19/0.49  cnf(c_0_125, plain, (v1_funct_2(k1_xboole_0,X1,X2)|~v1_partfun1(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_94]), c_0_115])])).
% 0.19/0.49  cnf(c_0_126, plain, (v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_116])).
% 0.19/0.49  cnf(c_0_127, negated_conjecture, (u1_struct_0(esk6_0)!=k1_xboole_0|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_107]), c_0_118])).
% 0.19/0.49  cnf(c_0_128, negated_conjecture, (v1_funct_2(esk8_0,X1,X2)|u1_struct_0(esk6_0)!=k1_xboole_0|u1_struct_0(esk6_0)!=X1|X1!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_107]), c_0_118])).
% 0.19/0.49  cnf(c_0_129, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.49  cnf(c_0_130, negated_conjecture, (v1_xboole_0(u1_struct_0(esk7_0))|v1_xboole_0(esk8_0)|~m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 0.19/0.49  cnf(c_0_131, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_122])).
% 0.19/0.49  cnf(c_0_132, negated_conjecture, (u1_struct_0(esk7_0)!=k1_xboole_0|~r2_hidden(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_72]), c_0_49])])).
% 0.19/0.49  cnf(c_0_133, plain, (v1_xboole_0(X1)|~v1_funct_2(k1_xboole_0,X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_94]), c_0_49])])).
% 0.19/0.49  cnf(c_0_134, plain, (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 0.19/0.49  cnf(c_0_135, negated_conjecture, (u1_struct_0(esk6_0)!=k1_xboole_0|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 0.19/0.49  cnf(c_0_136, negated_conjecture, (k1_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0),esk8_0)=u1_struct_0(esk6_0)|u1_struct_0(esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_34]), c_0_47])])).
% 0.19/0.49  cnf(c_0_137, negated_conjecture, (v1_xboole_0(u1_struct_0(esk7_0))|v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_70])])).
% 0.19/0.49  cnf(c_0_138, negated_conjecture, (v1_xboole_0(esk8_0)|u1_struct_0(esk7_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_132, c_0_91])).
% 0.19/0.49  cnf(c_0_139, plain, (k1_relat_1(k1_xboole_0)=X1|~v1_partfun1(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_104]), c_0_105])])).
% 0.19/0.49  cnf(c_0_140, plain, (v1_partfun1(k1_xboole_0,k1_relset_1(X1,X2,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_75]), c_0_94])])).
% 0.19/0.49  cnf(c_0_141, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 0.19/0.49  cnf(c_0_142, negated_conjecture, (u1_struct_0(esk6_0)!=k1_xboole_0|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_111]), c_0_54]), c_0_55])])).
% 0.19/0.49  cnf(c_0_143, negated_conjecture, (k1_relat_1(esk8_0)=u1_struct_0(esk6_0)|u1_struct_0(esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_136]), c_0_34])])).
% 0.19/0.49  cnf(c_0_144, negated_conjecture, (v1_xboole_0(esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_137]), c_0_138])).
% 0.19/0.49  cnf(c_0_145, plain, (k1_relat_1(k1_xboole_0)=k1_relset_1(X1,X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 0.19/0.49  cnf(c_0_146, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_141])).
% 0.19/0.49  cnf(c_0_147, negated_conjecture, (u1_struct_0(esk6_0)!=k1_xboole_0|~m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))), inference(spm,[status(thm)],[c_0_142, c_0_121])).
% 0.19/0.49  cnf(c_0_148, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.49  cnf(c_0_149, plain, (v1_funct_2(X1,X2,X3)|k1_relat_1(X1)!=X2|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_108, c_0_75])).
% 0.19/0.49  cnf(c_0_150, negated_conjecture, (k1_relset_1(X1,X2,esk8_0)=u1_struct_0(esk6_0)|u1_struct_0(esk7_0)=k1_xboole_0|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_75, c_0_143])).
% 0.19/0.49  cnf(c_0_151, negated_conjecture, (esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_144])).
% 0.19/0.49  cnf(c_0_152, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_145, c_0_146])).
% 0.19/0.49  cnf(c_0_153, negated_conjecture, (u1_struct_0(esk6_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_131]), c_0_55])])).
% 0.19/0.49  cnf(c_0_154, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,X2)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_148, c_0_94])).
% 0.19/0.49  cnf(c_0_155, plain, (v1_funct_2(k1_xboole_0,X1,X2)|k1_xboole_0!=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_94]), c_0_146])])).
% 0.19/0.49  cnf(c_0_156, negated_conjecture, (u1_struct_0(esk7_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_150, c_0_151]), c_0_152]), c_0_151]), c_0_94])]), c_0_153])).
% 0.19/0.49  cnf(c_0_157, plain, (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_154]), c_0_155])).
% 0.19/0.49  cnf(c_0_158, negated_conjecture, (~v2_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_151]), c_0_151]), c_0_94])]), c_0_156]), c_0_157])])).
% 0.19/0.49  cnf(c_0_159, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_111]), c_0_69]), c_0_70])])).
% 0.19/0.49  cnf(c_0_160, negated_conjecture, (~m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(spm,[status(thm)],[c_0_159, c_0_121])).
% 0.19/0.49  cnf(c_0_161, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_131]), c_0_70])]), ['proof']).
% 0.19/0.49  # SZS output end CNFRefutation
% 0.19/0.49  # Proof object total steps             : 162
% 0.19/0.49  # Proof object clause steps            : 120
% 0.19/0.49  # Proof object formula steps           : 42
% 0.19/0.49  # Proof object conjectures             : 69
% 0.19/0.49  # Proof object clause conjectures      : 66
% 0.19/0.49  # Proof object formula conjectures     : 3
% 0.19/0.49  # Proof object initial clauses used    : 40
% 0.19/0.49  # Proof object initial formulas used   : 21
% 0.19/0.49  # Proof object generating inferences   : 69
% 0.19/0.49  # Proof object simplifying inferences  : 137
% 0.19/0.49  # Training examples: 0 positive, 0 negative
% 0.19/0.49  # Parsed axioms                        : 23
% 0.19/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.49  # Initial clauses                      : 57
% 0.19/0.49  # Removed in clause preprocessing      : 4
% 0.19/0.49  # Initial clauses in saturation        : 53
% 0.19/0.49  # Processed clauses                    : 826
% 0.19/0.49  # ...of these trivial                  : 22
% 0.19/0.49  # ...subsumed                          : 302
% 0.19/0.49  # ...remaining for further processing  : 502
% 0.19/0.49  # Other redundant clauses eliminated   : 13
% 0.19/0.49  # Clauses deleted for lack of memory   : 0
% 0.19/0.49  # Backward-subsumed                    : 44
% 0.19/0.49  # Backward-rewritten                   : 226
% 0.19/0.49  # Generated clauses                    : 2269
% 0.19/0.49  # ...of the previous two non-trivial   : 2183
% 0.19/0.49  # Contextual simplify-reflections      : 32
% 0.19/0.49  # Paramodulations                      : 2195
% 0.19/0.49  # Factorizations                       : 53
% 0.19/0.49  # Equation resolutions                 : 21
% 0.19/0.49  # Propositional unsat checks           : 0
% 0.19/0.49  #    Propositional check models        : 0
% 0.19/0.49  #    Propositional check unsatisfiable : 0
% 0.19/0.49  #    Propositional clauses             : 0
% 0.19/0.49  #    Propositional clauses after purity: 0
% 0.19/0.49  #    Propositional unsat core size     : 0
% 0.19/0.49  #    Propositional preprocessing time  : 0.000
% 0.19/0.49  #    Propositional encoding time       : 0.000
% 0.19/0.49  #    Propositional solver time         : 0.000
% 0.19/0.49  #    Success case prop preproc time    : 0.000
% 0.19/0.49  #    Success case prop encoding time   : 0.000
% 0.19/0.49  #    Success case prop solver time     : 0.000
% 0.19/0.49  # Current number of processed clauses  : 228
% 0.19/0.49  #    Positive orientable unit clauses  : 20
% 0.19/0.49  #    Positive unorientable unit clauses: 0
% 0.19/0.49  #    Negative unit clauses             : 5
% 0.19/0.49  #    Non-unit-clauses                  : 203
% 0.19/0.49  # Current number of unprocessed clauses: 952
% 0.19/0.49  # ...number of literals in the above   : 5622
% 0.19/0.49  # Current number of archived formulas  : 0
% 0.19/0.49  # Current number of archived clauses   : 270
% 0.19/0.49  # Clause-clause subsumption calls (NU) : 39511
% 0.19/0.49  # Rec. Clause-clause subsumption calls : 12946
% 0.19/0.49  # Non-unit clause-clause subsumptions  : 335
% 0.19/0.49  # Unit Clause-clause subsumption calls : 1040
% 0.19/0.49  # Rewrite failures with RHS unbound    : 3
% 0.19/0.49  # BW rewrite match attempts            : 25
% 0.19/0.49  # BW rewrite match successes           : 11
% 0.19/0.49  # Condensation attempts                : 0
% 0.19/0.49  # Condensation successes               : 0
% 0.19/0.49  # Termbank termtop insertions          : 63151
% 0.19/0.49  
% 0.19/0.49  # -------------------------------------------------
% 0.19/0.49  # User time                : 0.143 s
% 0.19/0.49  # System time              : 0.011 s
% 0.19/0.49  # Total time               : 0.154 s
% 0.19/0.49  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
