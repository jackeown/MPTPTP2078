%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1885+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:09 EST 2020

% Result     : Theorem 16.05s
% Output     : CNFRefutation 16.05s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 189 expanded)
%              Number of clauses        :   21 (  64 expanded)
%              Number of leaves         :    5 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  138 (1365 expanded)
%              Number of equality atoms :   13 ( 121 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ ( v3_tex_2(X2,X1)
              & ! [X3] :
                  ( ( ~ v2_struct_0(X3)
                    & v1_pre_topc(X3)
                    & m1_pre_topc(X3,X1) )
                 => ~ ( v4_tex_2(X3,X1)
                      & X2 = u1_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',t29_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',dt_k1_pre_topc)).

fof(fc2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_struct_0(k1_pre_topc(X1,X2))
        & v1_pre_topc(k1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',fc2_pre_topc)).

fof(d8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v4_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ~ ( v3_tex_2(X2,X1)
                & ! [X3] :
                    ( ( ~ v2_struct_0(X3)
                      & v1_pre_topc(X3)
                      & m1_pre_topc(X3,X1) )
                   => ~ ( v4_tex_2(X3,X1)
                        & X2 = u1_struct_0(X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_tex_2])).

fof(c_0_6,plain,(
    ! [X5996,X5997] :
      ( ~ l1_pre_topc(X5996)
      | ~ m1_subset_1(X5997,k1_zfmisc_1(u1_struct_0(X5996)))
      | u1_struct_0(k1_pre_topc(X5996,X5997)) = X5997 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

fof(c_0_7,negated_conjecture,(
    ! [X11920] :
      ( ~ v2_struct_0(esk1365_0)
      & v2_pre_topc(esk1365_0)
      & l1_pre_topc(esk1365_0)
      & ~ v1_xboole_0(esk1366_0)
      & m1_subset_1(esk1366_0,k1_zfmisc_1(u1_struct_0(esk1365_0)))
      & v3_tex_2(esk1366_0,esk1365_0)
      & ( v2_struct_0(X11920)
        | ~ v1_pre_topc(X11920)
        | ~ m1_pre_topc(X11920,esk1365_0)
        | ~ v4_tex_2(X11920,esk1365_0)
        | esk1366_0 != u1_struct_0(X11920) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

fof(c_0_8,plain,(
    ! [X5911,X5912] :
      ( ( v1_pre_topc(k1_pre_topc(X5911,X5912))
        | ~ l1_pre_topc(X5911)
        | ~ m1_subset_1(X5912,k1_zfmisc_1(u1_struct_0(X5911))) )
      & ( m1_pre_topc(k1_pre_topc(X5911,X5912),X5911)
        | ~ l1_pre_topc(X5911)
        | ~ m1_subset_1(X5912,k1_zfmisc_1(u1_struct_0(X5911))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

fof(c_0_9,plain,(
    ! [X5930,X5931] :
      ( ( ~ v2_struct_0(k1_pre_topc(X5930,X5931))
        | v2_struct_0(X5930)
        | ~ l1_pre_topc(X5930)
        | v1_xboole_0(X5931)
        | ~ m1_subset_1(X5931,k1_zfmisc_1(u1_struct_0(X5930))) )
      & ( v1_pre_topc(k1_pre_topc(X5930,X5931))
        | v2_struct_0(X5930)
        | ~ l1_pre_topc(X5930)
        | v1_xboole_0(X5931)
        | ~ m1_subset_1(X5931,k1_zfmisc_1(u1_struct_0(X5930))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_pre_topc])])])])).

cnf(c_0_10,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk1366_0,k1_zfmisc_1(u1_struct_0(esk1365_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk1365_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | ~ v2_struct_0(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1365_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( ~ v1_xboole_0(esk1366_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk1365_0)
    | ~ v4_tex_2(X1,esk1365_0)
    | esk1366_0 != u1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk1365_0,esk1366_0)) = esk1366_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_19,negated_conjecture,
    ( v1_pre_topc(k1_pre_topc(esk1365_0,esk1366_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_11]),c_0_12])])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(k1_pre_topc(esk1365_0,esk1366_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_11]),c_0_12])]),c_0_15]),c_0_16])).

cnf(c_0_21,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_22,plain,(
    ! [X11709,X11710,X11711] :
      ( ( ~ v4_tex_2(X11710,X11709)
        | ~ m1_subset_1(X11711,k1_zfmisc_1(u1_struct_0(X11709)))
        | X11711 != u1_struct_0(X11710)
        | v3_tex_2(X11711,X11709)
        | ~ m1_pre_topc(X11710,X11709)
        | v2_struct_0(X11709)
        | ~ l1_pre_topc(X11709) )
      & ( m1_subset_1(esk1310_2(X11709,X11710),k1_zfmisc_1(u1_struct_0(X11709)))
        | v4_tex_2(X11710,X11709)
        | ~ m1_pre_topc(X11710,X11709)
        | v2_struct_0(X11709)
        | ~ l1_pre_topc(X11709) )
      & ( esk1310_2(X11709,X11710) = u1_struct_0(X11710)
        | v4_tex_2(X11710,X11709)
        | ~ m1_pre_topc(X11710,X11709)
        | v2_struct_0(X11709)
        | ~ l1_pre_topc(X11709) )
      & ( ~ v3_tex_2(esk1310_2(X11709,X11710),X11709)
        | v4_tex_2(X11710,X11709)
        | ~ m1_pre_topc(X11710,X11709)
        | v2_struct_0(X11709)
        | ~ l1_pre_topc(X11709) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tex_2])])])])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ v4_tex_2(k1_pre_topc(esk1365_0,esk1366_0),esk1365_0)
    | ~ m1_pre_topc(k1_pre_topc(esk1365_0,esk1366_0),esk1365_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk1365_0,esk1366_0),esk1365_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_11]),c_0_12])])).

cnf(c_0_25,plain,
    ( v4_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ v3_tex_2(esk1310_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( ~ v4_tex_2(k1_pre_topc(esk1365_0,esk1366_0),esk1365_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_27,plain,
    ( esk1310_2(X1,X2) = u1_struct_0(X2)
    | v4_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( ~ v3_tex_2(esk1310_2(esk1365_0,k1_pre_topc(esk1365_0,esk1366_0)),esk1365_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_12])]),c_0_26]),c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( esk1310_2(esk1365_0,k1_pre_topc(esk1365_0,esk1366_0)) = esk1366_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_18]),c_0_12])]),c_0_26]),c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( v3_tex_2(esk1366_0,esk1365_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
