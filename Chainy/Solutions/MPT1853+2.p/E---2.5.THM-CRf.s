%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1853+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:08 EST 2020

% Result     : Theorem 11.71s
% Output     : CNFRefutation 11.71s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 336 expanded)
%              Number of clauses        :   50 ( 123 expanded)
%              Number of leaves         :   17 (  82 expanded)
%              Depth                    :   12
%              Number of atoms          :  293 (1443 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v1_tex_2(k1_tex_2(X1,X2),X1)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',dt_l1_pre_topc)).

fof(t7_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => v1_subset_1(k6_domain_1(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

fof(cc1_zfmisc_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_zfmisc_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',cc1_zfmisc_1)).

fof(d3_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT028+2.ax',t1_tsep_1)).

fof(cc1_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( v1_subset_1(X2,X1)
           => v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_2)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',cc1_subset_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',fc2_struct_0)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(fc7_struct_0,axiom,(
    ! [X1] :
      ( ( v7_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',fc7_struct_0)).

fof(cc10_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v7_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ~ v2_struct_0(X2)
           => ( ~ v2_struct_0(X2)
              & ~ v1_tex_2(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).

fof(t8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
              & v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

fof(fc6_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v7_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',fc6_struct_0)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_18,plain,(
    ! [X11626,X11627] :
      ( ( ~ v2_struct_0(k1_tex_2(X11626,X11627))
        | v2_struct_0(X11626)
        | ~ l1_pre_topc(X11626)
        | ~ m1_subset_1(X11627,u1_struct_0(X11626)) )
      & ( v1_pre_topc(k1_tex_2(X11626,X11627))
        | v2_struct_0(X11626)
        | ~ l1_pre_topc(X11626)
        | ~ m1_subset_1(X11627,u1_struct_0(X11626)) )
      & ( m1_pre_topc(k1_tex_2(X11626,X11627),X11626)
        | v2_struct_0(X11626)
        | ~ l1_pre_topc(X11626)
        | ~ m1_subset_1(X11627,u1_struct_0(X11626)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk1330_0)
    & l1_pre_topc(esk1330_0)
    & m1_subset_1(esk1331_0,u1_struct_0(esk1330_0))
    & ( ~ v1_tex_2(k1_tex_2(esk1330_0,esk1331_0),esk1330_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk1330_0),esk1331_0),u1_struct_0(esk1330_0)) )
    & ( v1_tex_2(k1_tex_2(esk1330_0,esk1331_0),esk1330_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk1330_0),esk1331_0),u1_struct_0(esk1330_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_20,plain,(
    ! [X5918,X5919] :
      ( ~ l1_pre_topc(X5918)
      | ~ m1_pre_topc(X5919,X5918)
      | l1_pre_topc(X5919) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_21,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk1331_0,u1_struct_0(esk1330_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk1330_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1330_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X5917] :
      ( ~ l1_pre_topc(X5917)
      | l1_struct_0(X5917) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_26,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk1330_0,esk1331_0),esk1330_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])]),c_0_24])).

fof(c_0_28,plain,(
    ! [X11699,X11700] :
      ( v1_xboole_0(X11699)
      | v1_zfmisc_1(X11699)
      | ~ m1_subset_1(X11700,X11699)
      | v1_subset_1(k6_domain_1(X11699,X11700),X11699) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).

fof(c_0_29,plain,(
    ! [X989] :
      ( ~ v1_xboole_0(X989)
      | v1_zfmisc_1(X989) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).

fof(c_0_30,plain,(
    ! [X11617,X11618,X11619] :
      ( ( ~ v1_tex_2(X11618,X11617)
        | ~ m1_subset_1(X11619,k1_zfmisc_1(u1_struct_0(X11617)))
        | X11619 != u1_struct_0(X11618)
        | v1_subset_1(X11619,u1_struct_0(X11617))
        | ~ m1_pre_topc(X11618,X11617)
        | ~ l1_pre_topc(X11617) )
      & ( m1_subset_1(esk1303_2(X11617,X11618),k1_zfmisc_1(u1_struct_0(X11617)))
        | v1_tex_2(X11618,X11617)
        | ~ m1_pre_topc(X11618,X11617)
        | ~ l1_pre_topc(X11617) )
      & ( esk1303_2(X11617,X11618) = u1_struct_0(X11618)
        | v1_tex_2(X11618,X11617)
        | ~ m1_pre_topc(X11618,X11617)
        | ~ l1_pre_topc(X11617) )
      & ( ~ v1_subset_1(esk1303_2(X11617,X11618),u1_struct_0(X11617))
        | v1_tex_2(X11618,X11617)
        | ~ m1_pre_topc(X11618,X11617)
        | ~ l1_pre_topc(X11617) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_31,plain,(
    ! [X11076,X11077] :
      ( ~ l1_pre_topc(X11076)
      | ~ m1_pre_topc(X11077,X11076)
      | m1_subset_1(u1_struct_0(X11077),k1_zfmisc_1(u1_struct_0(X11076))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_32,plain,(
    ! [X11579,X11580] :
      ( v1_xboole_0(X11579)
      | ~ v1_zfmisc_1(X11579)
      | ~ m1_subset_1(X11580,k1_zfmisc_1(X11579))
      | ~ v1_subset_1(X11580,X11579)
      | v1_xboole_0(X11580) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_tex_2])])])])).

fof(c_0_33,plain,(
    ! [X1836,X1837] :
      ( ~ v1_xboole_0(X1836)
      | ~ m1_subset_1(X1837,k1_zfmisc_1(X1836))
      | v1_xboole_0(X1837) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_34,plain,(
    ! [X5932] :
      ( v2_struct_0(X5932)
      | ~ l1_struct_0(X5932)
      | ~ v1_xboole_0(u1_struct_0(X5932)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_35,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(k1_tex_2(esk1330_0,esk1331_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_23])])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( v1_zfmisc_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk1303_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( esk1303_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_42,plain,(
    ! [X11624,X11625] :
      ( ( ~ v1_subset_1(X11625,X11624)
        | X11625 != X11624
        | ~ m1_subset_1(X11625,k1_zfmisc_1(X11624)) )
      & ( X11625 = X11624
        | v1_subset_1(X11625,X11624)
        | ~ m1_subset_1(X11625,k1_zfmisc_1(X11624)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_43,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( l1_struct_0(k1_tex_2(esk1330_0,esk1331_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_struct_0(k1_tex_2(esk1330_0,esk1331_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_22]),c_0_23])]),c_0_24])).

fof(c_0_49,plain,(
    ! [X11630,X11631] :
      ( ( ~ v2_struct_0(k1_tex_2(X11630,X11631))
        | v2_struct_0(X11630)
        | ~ l1_pre_topc(X11630)
        | ~ m1_subset_1(X11631,u1_struct_0(X11630)) )
      & ( v7_struct_0(k1_tex_2(X11630,X11631))
        | v2_struct_0(X11630)
        | ~ l1_pre_topc(X11630)
        | ~ m1_subset_1(X11631,u1_struct_0(X11630)) )
      & ( v1_pre_topc(k1_tex_2(X11630,X11631))
        | v2_struct_0(X11630)
        | ~ l1_pre_topc(X11630)
        | ~ m1_subset_1(X11631,u1_struct_0(X11630)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

cnf(c_0_50,plain,
    ( v1_subset_1(k6_domain_1(X1,X2),X1)
    | v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk1330_0,esk1331_0),esk1330_0)
    | ~ v1_subset_1(esk1303_2(esk1330_0,k1_tex_2(esk1330_0,esk1331_0)),u1_struct_0(esk1330_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_27]),c_0_23])])).

cnf(c_0_52,negated_conjecture,
    ( esk1303_2(esk1330_0,k1_tex_2(esk1330_0,esk1331_0)) = u1_struct_0(k1_tex_2(esk1330_0,esk1331_0))
    | v1_tex_2(k1_tex_2(esk1330_0,esk1331_0),esk1330_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_27]),c_0_23])])).

cnf(c_0_53,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(u1_struct_0(k1_tex_2(esk1330_0,esk1331_0)),k1_zfmisc_1(u1_struct_0(esk1330_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_27]),c_0_23])])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_zfmisc_1(X2) ),
    inference(csr,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(k1_tex_2(esk1330_0,esk1331_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

fof(c_0_57,plain,(
    ! [X5942] :
      ( ~ v7_struct_0(X5942)
      | ~ l1_struct_0(X5942)
      | v1_zfmisc_1(u1_struct_0(X5942)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_58,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk1330_0,esk1331_0),esk1330_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk1330_0),esk1331_0),u1_struct_0(esk1330_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(esk1330_0),esk1331_0),u1_struct_0(esk1330_0))
    | v1_zfmisc_1(u1_struct_0(esk1330_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk1330_0,esk1331_0),esk1330_0)
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(esk1330_0,esk1331_0)),u1_struct_0(esk1330_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk1330_0,esk1331_0)) = u1_struct_0(esk1330_0)
    | v1_subset_1(u1_struct_0(k1_tex_2(esk1330_0,esk1331_0)),u1_struct_0(esk1330_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(esk1330_0,esk1331_0)),u1_struct_0(esk1330_0))
    | ~ v1_zfmisc_1(u1_struct_0(esk1330_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_54]),c_0_56])).

fof(c_0_64,plain,(
    ! [X11566,X11567] :
      ( ( ~ v2_struct_0(X11567)
        | v2_struct_0(X11567)
        | ~ m1_pre_topc(X11567,X11566)
        | v2_struct_0(X11566)
        | ~ v7_struct_0(X11566)
        | ~ l1_pre_topc(X11566) )
      & ( ~ v1_tex_2(X11567,X11566)
        | v2_struct_0(X11567)
        | ~ m1_pre_topc(X11567,X11566)
        | v2_struct_0(X11566)
        | ~ v7_struct_0(X11566)
        | ~ l1_pre_topc(X11566) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).

fof(c_0_65,plain,(
    ! [X11701,X11702] :
      ( v2_struct_0(X11701)
      | ~ l1_struct_0(X11701)
      | ~ m1_subset_1(X11702,u1_struct_0(X11701))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X11701),X11702),u1_struct_0(X11701))
      | ~ v7_struct_0(X11701) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).

fof(c_0_66,plain,(
    ! [X5940] :
      ( v7_struct_0(X5940)
      | ~ l1_struct_0(X5940)
      | ~ v1_zfmisc_1(u1_struct_0(X5940)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).

cnf(c_0_67,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( v7_struct_0(k1_tex_2(esk1330_0,esk1331_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_69,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk1330_0))
    | ~ v1_tex_2(k1_tex_2(esk1330_0,esk1331_0),esk1330_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk1330_0,esk1331_0)) = u1_struct_0(esk1330_0)
    | v1_tex_2(k1_tex_2(esk1330_0,esk1331_0),esk1330_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk1330_0,esk1331_0)) = u1_struct_0(esk1330_0)
    | ~ v1_zfmisc_1(u1_struct_0(esk1330_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_62])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v7_struct_0(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ v7_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( l1_struct_0(esk1330_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_23])).

cnf(c_0_75,plain,
    ( v7_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_zfmisc_1(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(k1_tex_2(esk1330_0,esk1331_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_47]),c_0_68])])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk1330_0,esk1331_0)) = u1_struct_0(esk1330_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk1330_0,esk1331_0),esk1330_0)
    | ~ v7_struct_0(esk1330_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_27]),c_0_23])]),c_0_24]),c_0_48])).

cnf(c_0_79,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk1330_0,esk1331_0),esk1330_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk1330_0),esk1331_0),u1_struct_0(esk1330_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_80,negated_conjecture,
    ( ~ v7_struct_0(esk1330_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk1330_0),esk1331_0),u1_struct_0(esk1330_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_22]),c_0_74])]),c_0_24])).

cnf(c_0_81,negated_conjecture,
    ( v7_struct_0(esk1330_0)
    | ~ v1_zfmisc_1(u1_struct_0(esk1330_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk1330_0)) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( ~ v7_struct_0(esk1330_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])]),c_0_83]),
    [proof]).
%------------------------------------------------------------------------------
