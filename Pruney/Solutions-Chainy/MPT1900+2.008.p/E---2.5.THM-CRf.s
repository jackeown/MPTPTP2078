%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:00 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 688 expanded)
%              Number of clauses        :   71 ( 261 expanded)
%              Number of leaves         :   28 ( 174 expanded)
%              Depth                    :   15
%              Number of atoms          :  460 (3857 expanded)
%              Number of equality atoms :   66 ( 146 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t68_tex_2,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => v5_pre_topc(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).

fof(t17_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(t55_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_struct_0(X2) = k1_xboole_0
                 => k2_struct_0(X1) = k1_xboole_0 )
               => ( v5_pre_topc(X3,X1,X2)
                <=> ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( v3_pre_topc(X4,X2)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t56_tops_2,axiom,(
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
             => ( v5_pre_topc(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_2)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

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

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(l222_relat_1,axiom,(
    ! [X1,X2] :
      ( v4_relat_1(k1_xboole_0,X1)
      & v5_relat_1(k1_xboole_0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t18_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => v5_pre_topc(X3,X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t68_tex_2])).

fof(c_0_29,plain,(
    ! [X63,X64] :
      ( ( ~ v1_tdlat_3(X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))
        | v3_pre_topc(X64,X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63) )
      & ( m1_subset_1(esk5_1(X63),k1_zfmisc_1(u1_struct_0(X63)))
        | v1_tdlat_3(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63) )
      & ( ~ v3_pre_topc(esk5_1(X63),X63)
        | v1_tdlat_3(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).

fof(c_0_30,plain,(
    ! [X62] :
      ( ~ l1_pre_topc(X62)
      | ~ v1_tdlat_3(X62)
      | v2_pre_topc(X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

fof(c_0_31,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | m1_subset_1(k8_relset_1(X33,X34,X35,X36),k1_zfmisc_1(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

fof(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk7_0)
    & v1_tdlat_3(esk7_0)
    & l1_pre_topc(esk7_0)
    & v2_pre_topc(esk8_0)
    & l1_pre_topc(esk8_0)
    & v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))))
    & ~ v5_pre_topc(esk9_0,esk7_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

fof(c_0_33,plain,(
    ! [X52,X53,X54,X55] :
      ( ( ~ v5_pre_topc(X54,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X53)))
        | ~ v3_pre_topc(X55,X53)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X52),u1_struct_0(X53),X54,X55),X52)
        | k2_struct_0(X53) = k1_xboole_0
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53))))
        | ~ l1_pre_topc(X53)
        | ~ l1_pre_topc(X52) )
      & ( m1_subset_1(esk3_3(X52,X53,X54),k1_zfmisc_1(u1_struct_0(X53)))
        | v5_pre_topc(X54,X52,X53)
        | k2_struct_0(X53) = k1_xboole_0
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53))))
        | ~ l1_pre_topc(X53)
        | ~ l1_pre_topc(X52) )
      & ( v3_pre_topc(esk3_3(X52,X53,X54),X53)
        | v5_pre_topc(X54,X52,X53)
        | k2_struct_0(X53) = k1_xboole_0
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53))))
        | ~ l1_pre_topc(X53)
        | ~ l1_pre_topc(X52) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X52),u1_struct_0(X53),X54,esk3_3(X52,X53,X54)),X52)
        | v5_pre_topc(X54,X52,X53)
        | k2_struct_0(X53) = k1_xboole_0
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53))))
        | ~ l1_pre_topc(X53)
        | ~ l1_pre_topc(X52) )
      & ( ~ v5_pre_topc(X54,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X53)))
        | ~ v3_pre_topc(X55,X53)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X52),u1_struct_0(X53),X54,X55),X52)
        | k2_struct_0(X52) != k1_xboole_0
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53))))
        | ~ l1_pre_topc(X53)
        | ~ l1_pre_topc(X52) )
      & ( m1_subset_1(esk3_3(X52,X53,X54),k1_zfmisc_1(u1_struct_0(X53)))
        | v5_pre_topc(X54,X52,X53)
        | k2_struct_0(X52) != k1_xboole_0
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53))))
        | ~ l1_pre_topc(X53)
        | ~ l1_pre_topc(X52) )
      & ( v3_pre_topc(esk3_3(X52,X53,X54),X53)
        | v5_pre_topc(X54,X52,X53)
        | k2_struct_0(X52) != k1_xboole_0
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53))))
        | ~ l1_pre_topc(X53)
        | ~ l1_pre_topc(X52) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X52),u1_struct_0(X53),X54,esk3_3(X52,X53,X54)),X52)
        | v5_pre_topc(X54,X52,X53)
        | k2_struct_0(X52) != k1_xboole_0
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53))))
        | ~ l1_pre_topc(X53)
        | ~ l1_pre_topc(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).

cnf(c_0_34,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( ~ v5_pre_topc(esk9_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,X1),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( v1_tdlat_3(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_47,plain,(
    ! [X49] :
      ( v2_struct_0(X49)
      | ~ l1_struct_0(X49)
      | ~ v1_xboole_0(k2_struct_0(X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_48,negated_conjecture,
    ( k2_struct_0(esk8_0) = k1_xboole_0
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk3_3(esk7_0,esk8_0,esk9_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_37])]),c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,X1),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_42])])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( k2_struct_0(esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_52,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_53,plain,(
    ! [X47] :
      ( ~ l1_pre_topc(X47)
      | l1_struct_0(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_54,plain,(
    ! [X48] :
      ( ~ v2_struct_0(X48)
      | ~ l1_struct_0(X48)
      | v1_xboole_0(u1_struct_0(X48)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

cnf(c_0_55,negated_conjecture,
    ( v2_struct_0(esk8_0)
    | ~ l1_struct_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_56,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_57,plain,(
    ! [X45] :
      ( v1_partfun1(k6_partfun1(X45),X45)
      & m1_subset_1(k6_partfun1(X45),k1_zfmisc_1(k2_zfmisc_1(X45,X45))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_58,plain,(
    ! [X46] : k6_partfun1(X46) = k6_relat_1(X46) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_59,plain,(
    ! [X18,X19] :
      ( ( k2_zfmisc_1(X18,X19) != k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_60,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_61,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_62,plain,(
    ! [X57,X58,X59,X60] :
      ( ( ~ v5_pre_topc(X59,X57,X58)
        | ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X58)))
        | r1_tarski(k2_pre_topc(X57,k8_relset_1(u1_struct_0(X57),u1_struct_0(X58),X59,X60)),k8_relset_1(u1_struct_0(X57),u1_struct_0(X58),X59,k2_pre_topc(X58,X60)))
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,u1_struct_0(X57),u1_struct_0(X58))
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X57),u1_struct_0(X58))))
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58)
        | ~ v2_pre_topc(X57)
        | ~ l1_pre_topc(X57) )
      & ( m1_subset_1(esk4_3(X57,X58,X59),k1_zfmisc_1(u1_struct_0(X58)))
        | v5_pre_topc(X59,X57,X58)
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,u1_struct_0(X57),u1_struct_0(X58))
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X57),u1_struct_0(X58))))
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58)
        | ~ v2_pre_topc(X57)
        | ~ l1_pre_topc(X57) )
      & ( ~ r1_tarski(k2_pre_topc(X57,k8_relset_1(u1_struct_0(X57),u1_struct_0(X58),X59,esk4_3(X57,X58,X59))),k8_relset_1(u1_struct_0(X57),u1_struct_0(X58),X59,k2_pre_topc(X58,esk4_3(X57,X58,X59))))
        | v5_pre_topc(X59,X57,X58)
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,u1_struct_0(X57),u1_struct_0(X58))
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X57),u1_struct_0(X58))))
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58)
        | ~ v2_pre_topc(X57)
        | ~ l1_pre_topc(X57) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_2])])])])])).

fof(c_0_63,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_xboole_0(X30)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30)))
      | v1_xboole_0(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_64,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_41])])).

cnf(c_0_66,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_68,plain,(
    ! [X26,X27] : v1_relat_1(k2_zfmisc_1(X26,X27)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_69,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_70,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_71,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_72,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_73,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_74,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( v2_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_76,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_77,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_78,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk8_0))
    | ~ l1_struct_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_79,plain,(
    ! [X43,X44] :
      ( ( ~ v1_partfun1(X44,X43)
        | k1_relat_1(X44) = X43
        | ~ v1_relat_1(X44)
        | ~ v4_relat_1(X44,X43) )
      & ( k1_relat_1(X44) != X43
        | v1_partfun1(X44,X43)
        | ~ v1_relat_1(X44)
        | ~ v4_relat_1(X44,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_80,plain,
    ( v1_partfun1(k6_relat_1(X1),X1) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_81,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

fof(c_0_82,plain,(
    ! [X28,X29] :
      ( v4_relat_1(k1_xboole_0,X28)
      & v5_relat_1(k1_xboole_0,X29) ) ),
    inference(variable_rename,[status(thm)],[l222_relat_1])).

cnf(c_0_83,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_84,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_85,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk4_3(esk7_0,esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_39]),c_0_40]),c_0_75]),c_0_76]),c_0_41]),c_0_42]),c_0_37])]),c_0_43])).

fof(c_0_89,plain,(
    ! [X15] :
      ( ~ v1_xboole_0(X15)
      | X15 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_90,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | ~ v1_xboole_0(u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_37])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_56]),c_0_41])])).

fof(c_0_92,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k1_relset_1(X37,X38,X39) = k1_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_93,plain,(
    ! [X20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_94,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_95,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_96,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_97,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

fof(c_0_98,plain,(
    ! [X66,X67] :
      ( ( ~ v1_tdlat_3(X66)
        | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))
        | v4_pre_topc(X67,X66)
        | ~ v2_pre_topc(X66)
        | ~ l1_pre_topc(X66) )
      & ( m1_subset_1(esk6_1(X66),k1_zfmisc_1(u1_struct_0(X66)))
        | v1_tdlat_3(X66)
        | ~ v2_pre_topc(X66)
        | ~ l1_pre_topc(X66) )
      & ( ~ v4_pre_topc(esk6_1(X66),X66)
        | v1_tdlat_3(X66)
        | ~ v2_pre_topc(X66)
        | ~ l1_pre_topc(X66) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tdlat_3])])])])])).

cnf(c_0_99,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk4_3(X1,X2,X3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk4_3(X1,X2,X3))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_100,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(esk4_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_102,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_103,negated_conjecture,
    ( v1_xboole_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])])).

fof(c_0_104,plain,(
    ! [X40,X41,X42] :
      ( ( k7_relset_1(X40,X41,X42,X40) = k2_relset_1(X40,X41,X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( k8_relset_1(X40,X41,X42,X41) = k1_relset_1(X40,X41,X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

cnf(c_0_105,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_106,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_107,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),c_0_97])])).

fof(c_0_108,plain,(
    ! [X50,X51] :
      ( ( ~ v4_pre_topc(X51,X50)
        | k2_pre_topc(X50,X51) = X51
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))
        | ~ l1_pre_topc(X50) )
      & ( ~ v2_pre_topc(X50)
        | k2_pre_topc(X50,X51) != X51
        | v4_pre_topc(X51,X50)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))
        | ~ l1_pre_topc(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_109,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_110,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(esk7_0,k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk4_3(esk7_0,esk8_0,esk9_0))),k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,k2_pre_topc(esk8_0,esk4_3(esk7_0,esk8_0,esk9_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_39]),c_0_40]),c_0_75]),c_0_76]),c_0_41]),c_0_42]),c_0_37])]),c_0_43])).

cnf(c_0_111,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,esk9_0) = u1_struct_0(esk8_0)
    | ~ v1_xboole_0(u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_112,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_113,negated_conjecture,
    ( u1_struct_0(esk8_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_102,c_0_91])).

cnf(c_0_114,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_115,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_107])).

cnf(c_0_116,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_117,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_109,c_0_35])).

cnf(c_0_118,negated_conjecture,
    ( ~ v1_xboole_0(k2_pre_topc(esk7_0,k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk4_3(esk7_0,esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_86])).

cnf(c_0_119,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_91])]),c_0_112]),c_0_113])).

cnf(c_0_120,plain,
    ( k8_relset_1(X1,X2,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_106]),c_0_115])).

cnf(c_0_121,plain,
    ( k2_pre_topc(X1,k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_116,c_0_106])).

cnf(c_0_122,plain,
    ( v4_pre_topc(k1_xboole_0,X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_117,c_0_106])).

cnf(c_0_123,negated_conjecture,
    ( ~ v1_xboole_0(k2_pre_topc(esk7_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_112]),c_0_112]),c_0_113]),c_0_119]),c_0_120])).

cnf(c_0_124,plain,
    ( k2_pre_topc(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_125,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_52]),c_0_46]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.20/0.43  # and selection function SelectNewComplexAHPNS.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.032 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t68_tex_2, conjecture, ![X1]:(((v2_pre_topc(X1)&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>v5_pre_topc(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_tex_2)).
% 0.20/0.43  fof(t17_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 0.20/0.43  fof(cc1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 0.20/0.43  fof(dt_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 0.20/0.43  fof(t55_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v3_pre_topc(X4,X2)=>v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_2)).
% 0.20/0.43  fof(fc5_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 0.20/0.43  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.43  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.43  fof(fc1_struct_0, axiom, ![X1]:((v2_struct_0(X1)&l1_struct_0(X1))=>v1_xboole_0(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 0.20/0.43  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.20/0.43  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.20/0.43  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.43  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.43  fof(t56_tops_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_2)).
% 0.20/0.43  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.20/0.43  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.43  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.20/0.43  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.20/0.43  fof(l222_relat_1, axiom, ![X1, X2]:(v4_relat_1(k1_xboole_0,X1)&v5_relat_1(k1_xboole_0,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 0.20/0.43  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.43  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.43  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.43  fof(t18_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tdlat_3)).
% 0.20/0.43  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 0.20/0.43  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.20/0.43  fof(c_0_28, negated_conjecture, ~(![X1]:(((v2_pre_topc(X1)&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>v5_pre_topc(X3,X1,X2))))), inference(assume_negation,[status(cth)],[t68_tex_2])).
% 0.20/0.43  fof(c_0_29, plain, ![X63, X64]:((~v1_tdlat_3(X63)|(~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))|v3_pre_topc(X64,X63))|(~v2_pre_topc(X63)|~l1_pre_topc(X63)))&((m1_subset_1(esk5_1(X63),k1_zfmisc_1(u1_struct_0(X63)))|v1_tdlat_3(X63)|(~v2_pre_topc(X63)|~l1_pre_topc(X63)))&(~v3_pre_topc(esk5_1(X63),X63)|v1_tdlat_3(X63)|(~v2_pre_topc(X63)|~l1_pre_topc(X63))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).
% 0.20/0.43  fof(c_0_30, plain, ![X62]:(~l1_pre_topc(X62)|(~v1_tdlat_3(X62)|v2_pre_topc(X62))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).
% 0.20/0.43  fof(c_0_31, plain, ![X33, X34, X35, X36]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|m1_subset_1(k8_relset_1(X33,X34,X35,X36),k1_zfmisc_1(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).
% 0.20/0.43  fof(c_0_32, negated_conjecture, (((v2_pre_topc(esk7_0)&v1_tdlat_3(esk7_0))&l1_pre_topc(esk7_0))&((v2_pre_topc(esk8_0)&l1_pre_topc(esk8_0))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0)))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)))))&~v5_pre_topc(esk9_0,esk7_0,esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.20/0.43  fof(c_0_33, plain, ![X52, X53, X54, X55]:(((~v5_pre_topc(X54,X52,X53)|(~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X53)))|(~v3_pre_topc(X55,X53)|v3_pre_topc(k8_relset_1(u1_struct_0(X52),u1_struct_0(X53),X54,X55),X52)))|k2_struct_0(X53)=k1_xboole_0|(~v1_funct_1(X54)|~v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53)))))|~l1_pre_topc(X53)|~l1_pre_topc(X52))&((m1_subset_1(esk3_3(X52,X53,X54),k1_zfmisc_1(u1_struct_0(X53)))|v5_pre_topc(X54,X52,X53)|k2_struct_0(X53)=k1_xboole_0|(~v1_funct_1(X54)|~v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53)))))|~l1_pre_topc(X53)|~l1_pre_topc(X52))&((v3_pre_topc(esk3_3(X52,X53,X54),X53)|v5_pre_topc(X54,X52,X53)|k2_struct_0(X53)=k1_xboole_0|(~v1_funct_1(X54)|~v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53)))))|~l1_pre_topc(X53)|~l1_pre_topc(X52))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X52),u1_struct_0(X53),X54,esk3_3(X52,X53,X54)),X52)|v5_pre_topc(X54,X52,X53)|k2_struct_0(X53)=k1_xboole_0|(~v1_funct_1(X54)|~v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53)))))|~l1_pre_topc(X53)|~l1_pre_topc(X52)))))&((~v5_pre_topc(X54,X52,X53)|(~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X53)))|(~v3_pre_topc(X55,X53)|v3_pre_topc(k8_relset_1(u1_struct_0(X52),u1_struct_0(X53),X54,X55),X52)))|k2_struct_0(X52)!=k1_xboole_0|(~v1_funct_1(X54)|~v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53)))))|~l1_pre_topc(X53)|~l1_pre_topc(X52))&((m1_subset_1(esk3_3(X52,X53,X54),k1_zfmisc_1(u1_struct_0(X53)))|v5_pre_topc(X54,X52,X53)|k2_struct_0(X52)!=k1_xboole_0|(~v1_funct_1(X54)|~v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53)))))|~l1_pre_topc(X53)|~l1_pre_topc(X52))&((v3_pre_topc(esk3_3(X52,X53,X54),X53)|v5_pre_topc(X54,X52,X53)|k2_struct_0(X52)!=k1_xboole_0|(~v1_funct_1(X54)|~v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53)))))|~l1_pre_topc(X53)|~l1_pre_topc(X52))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X52),u1_struct_0(X53),X54,esk3_3(X52,X53,X54)),X52)|v5_pre_topc(X54,X52,X53)|k2_struct_0(X52)!=k1_xboole_0|(~v1_funct_1(X54)|~v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53)))))|~l1_pre_topc(X53)|~l1_pre_topc(X52)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).
% 0.20/0.43  cnf(c_0_34, plain, (v3_pre_topc(X2,X1)|~v1_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_35, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.43  cnf(c_0_36, plain, (m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.43  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_38, plain, (v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_3(X1,X2,X3)),X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.43  cnf(c_0_39, negated_conjecture, (v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_40, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_42, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_43, negated_conjecture, (~v5_pre_topc(esk9_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_44, plain, (v3_pre_topc(X1,X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.43  cnf(c_0_45, negated_conjecture, (m1_subset_1(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,X1),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.43  cnf(c_0_46, negated_conjecture, (v1_tdlat_3(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  fof(c_0_47, plain, ![X49]:(v2_struct_0(X49)|~l1_struct_0(X49)|~v1_xboole_0(k2_struct_0(X49))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).
% 0.20/0.43  cnf(c_0_48, negated_conjecture, (k2_struct_0(esk8_0)=k1_xboole_0|~v3_pre_topc(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk3_3(esk7_0,esk8_0,esk9_0)),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_37])]), c_0_43])).
% 0.20/0.43  cnf(c_0_49, negated_conjecture, (v3_pre_topc(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,X1),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_42])])).
% 0.20/0.43  cnf(c_0_50, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(k2_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.43  cnf(c_0_51, negated_conjecture, (k2_struct_0(esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49])])).
% 0.20/0.43  cnf(c_0_52, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.43  fof(c_0_53, plain, ![X47]:(~l1_pre_topc(X47)|l1_struct_0(X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.43  fof(c_0_54, plain, ![X48]:(~v2_struct_0(X48)|~l1_struct_0(X48)|v1_xboole_0(u1_struct_0(X48))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).
% 0.20/0.43  cnf(c_0_55, negated_conjecture, (v2_struct_0(esk8_0)|~l1_struct_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.20/0.43  cnf(c_0_56, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.43  fof(c_0_57, plain, ![X45]:(v1_partfun1(k6_partfun1(X45),X45)&m1_subset_1(k6_partfun1(X45),k1_zfmisc_1(k2_zfmisc_1(X45,X45)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.20/0.43  fof(c_0_58, plain, ![X46]:k6_partfun1(X46)=k6_relat_1(X46), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.20/0.43  fof(c_0_59, plain, ![X18, X19]:((k2_zfmisc_1(X18,X19)!=k1_xboole_0|(X18=k1_xboole_0|X19=k1_xboole_0))&((X18!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0)&(X19!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.43  fof(c_0_60, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.43  fof(c_0_61, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.43  fof(c_0_62, plain, ![X57, X58, X59, X60]:((~v5_pre_topc(X59,X57,X58)|(~m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X58)))|r1_tarski(k2_pre_topc(X57,k8_relset_1(u1_struct_0(X57),u1_struct_0(X58),X59,X60)),k8_relset_1(u1_struct_0(X57),u1_struct_0(X58),X59,k2_pre_topc(X58,X60))))|(~v1_funct_1(X59)|~v1_funct_2(X59,u1_struct_0(X57),u1_struct_0(X58))|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X57),u1_struct_0(X58)))))|(~v2_pre_topc(X58)|~l1_pre_topc(X58))|(~v2_pre_topc(X57)|~l1_pre_topc(X57)))&((m1_subset_1(esk4_3(X57,X58,X59),k1_zfmisc_1(u1_struct_0(X58)))|v5_pre_topc(X59,X57,X58)|(~v1_funct_1(X59)|~v1_funct_2(X59,u1_struct_0(X57),u1_struct_0(X58))|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X57),u1_struct_0(X58)))))|(~v2_pre_topc(X58)|~l1_pre_topc(X58))|(~v2_pre_topc(X57)|~l1_pre_topc(X57)))&(~r1_tarski(k2_pre_topc(X57,k8_relset_1(u1_struct_0(X57),u1_struct_0(X58),X59,esk4_3(X57,X58,X59))),k8_relset_1(u1_struct_0(X57),u1_struct_0(X58),X59,k2_pre_topc(X58,esk4_3(X57,X58,X59))))|v5_pre_topc(X59,X57,X58)|(~v1_funct_1(X59)|~v1_funct_2(X59,u1_struct_0(X57),u1_struct_0(X58))|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X57),u1_struct_0(X58)))))|(~v2_pre_topc(X58)|~l1_pre_topc(X58))|(~v2_pre_topc(X57)|~l1_pre_topc(X57))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_2])])])])])).
% 0.20/0.43  fof(c_0_63, plain, ![X30, X31, X32]:(~v1_xboole_0(X30)|(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30)))|v1_xboole_0(X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.20/0.43  cnf(c_0_64, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.43  cnf(c_0_65, negated_conjecture, (v2_struct_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_41])])).
% 0.20/0.43  cnf(c_0_66, plain, (v1_partfun1(k6_partfun1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.43  cnf(c_0_67, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.43  fof(c_0_68, plain, ![X26, X27]:v1_relat_1(k2_zfmisc_1(X26,X27)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.43  cnf(c_0_69, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.43  fof(c_0_70, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.43  cnf(c_0_71, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.43  cnf(c_0_72, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.43  fof(c_0_73, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.43  cnf(c_0_74, plain, (m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.43  cnf(c_0_75, negated_conjecture, (v2_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_76, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_77, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.43  cnf(c_0_78, negated_conjecture, (v1_xboole_0(u1_struct_0(esk8_0))|~l1_struct_0(esk8_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.43  fof(c_0_79, plain, ![X43, X44]:((~v1_partfun1(X44,X43)|k1_relat_1(X44)=X43|(~v1_relat_1(X44)|~v4_relat_1(X44,X43)))&(k1_relat_1(X44)!=X43|v1_partfun1(X44,X43)|(~v1_relat_1(X44)|~v4_relat_1(X44,X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.20/0.43  cnf(c_0_80, plain, (v1_partfun1(k6_relat_1(X1),X1)), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.43  cnf(c_0_81, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.20/0.43  fof(c_0_82, plain, ![X28, X29]:(v4_relat_1(k1_xboole_0,X28)&v5_relat_1(k1_xboole_0,X29)), inference(variable_rename,[status(thm)],[l222_relat_1])).
% 0.20/0.43  cnf(c_0_83, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.43  cnf(c_0_84, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_69])).
% 0.20/0.43  cnf(c_0_85, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.43  cnf(c_0_86, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.43  cnf(c_0_87, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.43  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk4_3(esk7_0,esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_39]), c_0_40]), c_0_75]), c_0_76]), c_0_41]), c_0_42]), c_0_37])]), c_0_43])).
% 0.20/0.43  fof(c_0_89, plain, ![X15]:(~v1_xboole_0(X15)|X15=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.43  cnf(c_0_90, negated_conjecture, (v1_xboole_0(esk9_0)|~v1_xboole_0(u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_77, c_0_37])).
% 0.20/0.43  cnf(c_0_91, negated_conjecture, (v1_xboole_0(u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_56]), c_0_41])])).
% 0.20/0.43  fof(c_0_92, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k1_relset_1(X37,X38,X39)=k1_relat_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.43  fof(c_0_93, plain, ![X20]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.43  cnf(c_0_94, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.43  cnf(c_0_95, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.20/0.43  cnf(c_0_96, plain, (v4_relat_1(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.43  cnf(c_0_97, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.43  fof(c_0_98, plain, ![X66, X67]:((~v1_tdlat_3(X66)|(~m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))|v4_pre_topc(X67,X66))|(~v2_pre_topc(X66)|~l1_pre_topc(X66)))&((m1_subset_1(esk6_1(X66),k1_zfmisc_1(u1_struct_0(X66)))|v1_tdlat_3(X66)|(~v2_pre_topc(X66)|~l1_pre_topc(X66)))&(~v4_pre_topc(esk6_1(X66),X66)|v1_tdlat_3(X66)|(~v2_pre_topc(X66)|~l1_pre_topc(X66))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tdlat_3])])])])])).
% 0.20/0.43  cnf(c_0_99, plain, (v5_pre_topc(X3,X1,X2)|~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk4_3(X1,X2,X3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk4_3(X1,X2,X3))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.43  cnf(c_0_100, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.20/0.43  cnf(c_0_101, negated_conjecture, (r1_tarski(esk4_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.20/0.43  cnf(c_0_102, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.43  cnf(c_0_103, negated_conjecture, (v1_xboole_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])])).
% 0.20/0.43  fof(c_0_104, plain, ![X40, X41, X42]:((k7_relset_1(X40,X41,X42,X40)=k2_relset_1(X40,X41,X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(k8_relset_1(X40,X41,X42,X41)=k1_relset_1(X40,X41,X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.20/0.43  cnf(c_0_105, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.20/0.43  cnf(c_0_106, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.20/0.43  cnf(c_0_107, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96]), c_0_97])])).
% 0.20/0.43  fof(c_0_108, plain, ![X50, X51]:((~v4_pre_topc(X51,X50)|k2_pre_topc(X50,X51)=X51|~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))|~l1_pre_topc(X50))&(~v2_pre_topc(X50)|k2_pre_topc(X50,X51)!=X51|v4_pre_topc(X51,X50)|~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))|~l1_pre_topc(X50))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.20/0.43  cnf(c_0_109, plain, (v4_pre_topc(X2,X1)|~v1_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.20/0.43  cnf(c_0_110, negated_conjecture, (~r1_tarski(k2_pre_topc(esk7_0,k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk4_3(esk7_0,esk8_0,esk9_0))),k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,k2_pre_topc(esk8_0,esk4_3(esk7_0,esk8_0,esk9_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_39]), c_0_40]), c_0_75]), c_0_76]), c_0_41]), c_0_42]), c_0_37])]), c_0_43])).
% 0.20/0.43  cnf(c_0_111, negated_conjecture, (esk4_3(esk7_0,esk8_0,esk9_0)=u1_struct_0(esk8_0)|~v1_xboole_0(u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.20/0.43  cnf(c_0_112, negated_conjecture, (esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.20/0.43  cnf(c_0_113, negated_conjecture, (u1_struct_0(esk8_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_102, c_0_91])).
% 0.20/0.43  cnf(c_0_114, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.20/0.43  cnf(c_0_115, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_107])).
% 0.20/0.43  cnf(c_0_116, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 0.20/0.43  cnf(c_0_117, plain, (v4_pre_topc(X1,X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_109, c_0_35])).
% 0.20/0.43  cnf(c_0_118, negated_conjecture, (~v1_xboole_0(k2_pre_topc(esk7_0,k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk4_3(esk7_0,esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_110, c_0_86])).
% 0.20/0.43  cnf(c_0_119, negated_conjecture, (esk4_3(esk7_0,esk8_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_91])]), c_0_112]), c_0_113])).
% 0.20/0.43  cnf(c_0_120, plain, (k8_relset_1(X1,X2,k1_xboole_0,X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_106]), c_0_115])).
% 0.20/0.43  cnf(c_0_121, plain, (k2_pre_topc(X1,k1_xboole_0)=k1_xboole_0|~v4_pre_topc(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_116, c_0_106])).
% 0.20/0.43  cnf(c_0_122, plain, (v4_pre_topc(k1_xboole_0,X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_117, c_0_106])).
% 0.20/0.43  cnf(c_0_123, negated_conjecture, (~v1_xboole_0(k2_pre_topc(esk7_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_112]), c_0_112]), c_0_113]), c_0_119]), c_0_120])).
% 0.20/0.43  cnf(c_0_124, plain, (k2_pre_topc(X1,k1_xboole_0)=k1_xboole_0|~v1_tdlat_3(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 0.20/0.43  cnf(c_0_125, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_52]), c_0_46]), c_0_42])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 126
% 0.20/0.43  # Proof object clause steps            : 71
% 0.20/0.43  # Proof object formula steps           : 55
% 0.20/0.43  # Proof object conjectures             : 32
% 0.20/0.43  # Proof object clause conjectures      : 29
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 37
% 0.20/0.43  # Proof object initial formulas used   : 28
% 0.20/0.43  # Proof object generating inferences   : 26
% 0.20/0.43  # Proof object simplifying inferences  : 57
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 29
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 63
% 0.20/0.43  # Removed in clause preprocessing      : 1
% 0.20/0.43  # Initial clauses in saturation        : 62
% 0.20/0.43  # Processed clauses                    : 487
% 0.20/0.43  # ...of these trivial                  : 9
% 0.20/0.43  # ...subsumed                          : 187
% 0.20/0.43  # ...remaining for further processing  : 291
% 0.20/0.43  # Other redundant clauses eliminated   : 19
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 1
% 0.20/0.43  # Backward-rewritten                   : 70
% 0.20/0.43  # Generated clauses                    : 1530
% 0.20/0.43  # ...of the previous two non-trivial   : 1381
% 0.20/0.43  # Contextual simplify-reflections      : 2
% 0.20/0.43  # Paramodulations                      : 1511
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 19
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 154
% 0.20/0.43  #    Positive orientable unit clauses  : 42
% 0.20/0.43  #    Positive unorientable unit clauses: 1
% 0.20/0.43  #    Negative unit clauses             : 2
% 0.20/0.43  #    Non-unit-clauses                  : 109
% 0.20/0.43  # Current number of unprocessed clauses: 1008
% 0.20/0.43  # ...number of literals in the above   : 4534
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 133
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 10031
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 2442
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 184
% 0.20/0.43  # Unit Clause-clause subsumption calls : 472
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 135
% 0.20/0.43  # BW rewrite match successes           : 15
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 27548
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.075 s
% 0.20/0.43  # System time              : 0.006 s
% 0.20/0.43  # Total time               : 0.081 s
% 0.20/0.43  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
