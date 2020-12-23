%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QTeBWLolVM

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:03 EST 2020

% Result     : Theorem 3.58s
% Output     : Refutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 140 expanded)
%              Number of leaves         :   33 (  55 expanded)
%              Depth                    :   22
%              Number of atoms          :  832 (1440 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(t46_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( v3_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['1','4'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) )
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) )
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_tex_2 @ X17 @ X18 )
      | ~ ( v2_tex_2 @ X19 @ X18 )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( X17 = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['5','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('38',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QTeBWLolVM
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:16:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 3.58/3.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.58/3.78  % Solved by: fo/fo7.sh
% 3.58/3.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.58/3.78  % done 2074 iterations in 3.332s
% 3.58/3.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.58/3.78  % SZS output start Refutation
% 3.58/3.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.58/3.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.58/3.78  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 3.58/3.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.58/3.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.58/3.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.58/3.78  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 3.58/3.78  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 3.58/3.78  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.58/3.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.58/3.78  thf(sk_B_type, type, sk_B: $i > $i).
% 3.58/3.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.58/3.78  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 3.58/3.78  thf(sk_A_type, type, sk_A: $i).
% 3.58/3.78  thf(sk_B_2_type, type, sk_B_2: $i).
% 3.58/3.78  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.58/3.78  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.58/3.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.58/3.78  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 3.58/3.78  thf(t46_tex_2, conjecture,
% 3.58/3.78    (![A:$i]:
% 3.58/3.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.58/3.78       ( ![B:$i]:
% 3.58/3.78         ( ( ( v1_xboole_0 @ B ) & 
% 3.58/3.78             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.58/3.78           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 3.58/3.78  thf(zf_stmt_0, negated_conjecture,
% 3.58/3.78    (~( ![A:$i]:
% 3.58/3.78        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.58/3.78            ( l1_pre_topc @ A ) ) =>
% 3.58/3.78          ( ![B:$i]:
% 3.58/3.78            ( ( ( v1_xboole_0 @ B ) & 
% 3.58/3.78                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.58/3.78              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 3.58/3.78    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 3.58/3.78  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 3.58/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.58/3.78  thf('1', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 3.58/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.58/3.78  thf('2', plain, ((v1_xboole_0 @ sk_B_2)),
% 3.58/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.58/3.78  thf(l13_xboole_0, axiom,
% 3.58/3.78    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.58/3.78  thf('3', plain,
% 3.58/3.78      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 3.58/3.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.58/3.78  thf('4', plain, (((sk_B_2) = (k1_xboole_0))),
% 3.58/3.78      inference('sup-', [status(thm)], ['2', '3'])).
% 3.58/3.78  thf('5', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 3.58/3.78      inference('demod', [status(thm)], ['1', '4'])).
% 3.58/3.78  thf(d1_xboole_0, axiom,
% 3.58/3.78    (![A:$i]:
% 3.58/3.78     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.58/3.78  thf('6', plain,
% 3.58/3.78      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.58/3.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.58/3.78  thf(rc7_pre_topc, axiom,
% 3.58/3.78    (![A:$i]:
% 3.58/3.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.58/3.78       ( ?[B:$i]:
% 3.58/3.78         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 3.58/3.78           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 3.58/3.78  thf('7', plain,
% 3.58/3.78      (![X12 : $i]:
% 3.58/3.78         ((m1_subset_1 @ (sk_B_1 @ X12) @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 3.58/3.78          | ~ (l1_pre_topc @ X12)
% 3.58/3.78          | ~ (v2_pre_topc @ X12)
% 3.58/3.78          | (v2_struct_0 @ X12))),
% 3.58/3.78      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 3.58/3.78  thf(t4_subset, axiom,
% 3.58/3.78    (![A:$i,B:$i,C:$i]:
% 3.58/3.78     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 3.58/3.78       ( m1_subset_1 @ A @ C ) ))).
% 3.58/3.78  thf('8', plain,
% 3.58/3.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.58/3.78         (~ (r2_hidden @ X9 @ X10)
% 3.58/3.78          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 3.58/3.78          | (m1_subset_1 @ X9 @ X11))),
% 3.58/3.78      inference('cnf', [status(esa)], [t4_subset])).
% 3.58/3.78  thf('9', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]:
% 3.58/3.78         ((v2_struct_0 @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 3.58/3.78          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 3.58/3.78      inference('sup-', [status(thm)], ['7', '8'])).
% 3.58/3.78  thf('10', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | (v2_struct_0 @ X0))),
% 3.58/3.78      inference('sup-', [status(thm)], ['6', '9'])).
% 3.58/3.78  thf(redefinition_k6_domain_1, axiom,
% 3.58/3.78    (![A:$i,B:$i]:
% 3.58/3.78     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 3.58/3.78       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 3.58/3.78  thf('11', plain,
% 3.58/3.78      (![X15 : $i, X16 : $i]:
% 3.58/3.78         ((v1_xboole_0 @ X15)
% 3.58/3.78          | ~ (m1_subset_1 @ X16 @ X15)
% 3.58/3.78          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 3.58/3.78      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 3.58/3.78  thf('12', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((v2_struct_0 @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | ((k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0)))
% 3.58/3.78              = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 3.58/3.78          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 3.58/3.78      inference('sup-', [status(thm)], ['10', '11'])).
% 3.58/3.78  thf('13', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | (v2_struct_0 @ X0))),
% 3.58/3.78      inference('sup-', [status(thm)], ['6', '9'])).
% 3.58/3.78  thf(t36_tex_2, axiom,
% 3.58/3.78    (![A:$i]:
% 3.58/3.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.58/3.78       ( ![B:$i]:
% 3.58/3.78         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.58/3.78           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 3.58/3.78  thf('14', plain,
% 3.58/3.78      (![X20 : $i, X21 : $i]:
% 3.58/3.78         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 3.58/3.78          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 3.58/3.78          | ~ (l1_pre_topc @ X21)
% 3.58/3.78          | ~ (v2_pre_topc @ X21)
% 3.58/3.78          | (v2_struct_0 @ X21))),
% 3.58/3.78      inference('cnf', [status(esa)], [t36_tex_2])).
% 3.58/3.78  thf('15', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((v2_struct_0 @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | (v2_struct_0 @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | (v2_tex_2 @ 
% 3.58/3.78             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ X0))),
% 3.58/3.78      inference('sup-', [status(thm)], ['13', '14'])).
% 3.58/3.78  thf('16', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((v2_tex_2 @ 
% 3.58/3.78           (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | (v2_struct_0 @ X0))),
% 3.58/3.78      inference('simplify', [status(thm)], ['15'])).
% 3.58/3.78  thf('17', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 3.58/3.78          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | (v2_struct_0 @ X0)
% 3.58/3.78          | (v2_struct_0 @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0)))),
% 3.58/3.78      inference('sup+', [status(thm)], ['12', '16'])).
% 3.58/3.78  thf('18', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((v2_struct_0 @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 3.58/3.78          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0))),
% 3.58/3.78      inference('simplify', [status(thm)], ['17'])).
% 3.58/3.78  thf('19', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((v2_struct_0 @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | ((k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0)))
% 3.58/3.78              = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 3.58/3.78          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 3.58/3.78      inference('sup-', [status(thm)], ['10', '11'])).
% 3.58/3.78  thf('20', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | (v2_struct_0 @ X0))),
% 3.58/3.78      inference('sup-', [status(thm)], ['6', '9'])).
% 3.58/3.78  thf(dt_k6_domain_1, axiom,
% 3.58/3.78    (![A:$i,B:$i]:
% 3.58/3.78     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 3.58/3.78       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.58/3.78  thf('21', plain,
% 3.58/3.78      (![X13 : $i, X14 : $i]:
% 3.58/3.78         ((v1_xboole_0 @ X13)
% 3.58/3.78          | ~ (m1_subset_1 @ X14 @ X13)
% 3.58/3.78          | (m1_subset_1 @ (k6_domain_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13)))),
% 3.58/3.78      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 3.58/3.78  thf('22', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((v2_struct_0 @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | (m1_subset_1 @ 
% 3.58/3.78             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ 
% 3.58/3.78             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 3.58/3.78          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 3.58/3.78      inference('sup-', [status(thm)], ['20', '21'])).
% 3.58/3.78  thf('23', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((m1_subset_1 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ 
% 3.58/3.78           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 3.58/3.78          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | (v2_struct_0 @ X0)
% 3.58/3.78          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | (v2_struct_0 @ X0))),
% 3.58/3.78      inference('sup+', [status(thm)], ['19', '22'])).
% 3.58/3.78  thf('24', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((v2_struct_0 @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 3.58/3.78          | (m1_subset_1 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ 
% 3.58/3.78             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 3.58/3.78      inference('simplify', [status(thm)], ['23'])).
% 3.58/3.78  thf(t4_subset_1, axiom,
% 3.58/3.78    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.58/3.78  thf('25', plain,
% 3.58/3.78      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 3.58/3.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.58/3.78  thf(d7_tex_2, axiom,
% 3.58/3.78    (![A:$i]:
% 3.58/3.78     ( ( l1_pre_topc @ A ) =>
% 3.58/3.78       ( ![B:$i]:
% 3.58/3.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.58/3.78           ( ( v3_tex_2 @ B @ A ) <=>
% 3.58/3.78             ( ( v2_tex_2 @ B @ A ) & 
% 3.58/3.78               ( ![C:$i]:
% 3.58/3.78                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.58/3.78                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 3.58/3.78                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 3.58/3.78  thf('26', plain,
% 3.58/3.78      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.58/3.78         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 3.58/3.78          | ~ (v3_tex_2 @ X17 @ X18)
% 3.58/3.78          | ~ (v2_tex_2 @ X19 @ X18)
% 3.58/3.78          | ~ (r1_tarski @ X17 @ X19)
% 3.58/3.78          | ((X17) = (X19))
% 3.58/3.78          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 3.58/3.78          | ~ (l1_pre_topc @ X18))),
% 3.58/3.78      inference('cnf', [status(esa)], [d7_tex_2])).
% 3.58/3.78  thf('27', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]:
% 3.58/3.78         (~ (l1_pre_topc @ X0)
% 3.58/3.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 3.58/3.78          | ((k1_xboole_0) = (X1))
% 3.58/3.78          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 3.58/3.78          | ~ (v2_tex_2 @ X1 @ X0)
% 3.58/3.78          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 3.58/3.78      inference('sup-', [status(thm)], ['25', '26'])).
% 3.58/3.78  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.58/3.78  thf('28', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 3.58/3.78      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.58/3.78  thf('29', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]:
% 3.58/3.78         (~ (l1_pre_topc @ X0)
% 3.58/3.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 3.58/3.78          | ((k1_xboole_0) = (X1))
% 3.58/3.78          | ~ (v2_tex_2 @ X1 @ X0)
% 3.58/3.78          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 3.58/3.78      inference('demod', [status(thm)], ['27', '28'])).
% 3.58/3.78  thf('30', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | (v2_struct_0 @ X0)
% 3.58/3.78          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 3.58/3.78          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 3.58/3.78          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 3.58/3.78          | ~ (l1_pre_topc @ X0))),
% 3.58/3.78      inference('sup-', [status(thm)], ['24', '29'])).
% 3.58/3.78  thf('31', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         (((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 3.58/3.78          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 3.58/3.78          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 3.58/3.78          | (v2_struct_0 @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 3.58/3.78      inference('simplify', [status(thm)], ['30'])).
% 3.58/3.78  thf('32', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | (v2_struct_0 @ X0)
% 3.58/3.78          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | (v2_struct_0 @ X0)
% 3.58/3.78          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 3.58/3.78          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ X0)))))),
% 3.58/3.78      inference('sup-', [status(thm)], ['18', '31'])).
% 3.58/3.78  thf('33', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         (((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 3.58/3.78          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 3.58/3.78          | (v2_struct_0 @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 3.58/3.78          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 3.58/3.78      inference('simplify', [status(thm)], ['32'])).
% 3.58/3.78  thf('34', plain,
% 3.58/3.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.58/3.78        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 3.58/3.78        | ~ (l1_pre_topc @ sk_A)
% 3.58/3.78        | ~ (v2_pre_topc @ sk_A)
% 3.58/3.78        | (v2_struct_0 @ sk_A)
% 3.58/3.78        | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ sk_A)))))),
% 3.58/3.78      inference('sup-', [status(thm)], ['5', '33'])).
% 3.58/3.78  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 3.58/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.58/3.78  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 3.58/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.58/3.78  thf('37', plain,
% 3.58/3.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.58/3.78        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 3.58/3.78        | (v2_struct_0 @ sk_A)
% 3.58/3.78        | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ sk_A)))))),
% 3.58/3.78      inference('demod', [status(thm)], ['34', '35', '36'])).
% 3.58/3.78  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 3.58/3.78  thf('38', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X5))),
% 3.58/3.78      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 3.58/3.78  thf('39', plain,
% 3.58/3.78      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.58/3.78        | (v2_struct_0 @ sk_A)
% 3.58/3.78        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 3.58/3.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 3.58/3.78      inference('sup-', [status(thm)], ['37', '38'])).
% 3.58/3.78  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.58/3.78  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.58/3.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.58/3.78  thf('41', plain,
% 3.58/3.78      (((v2_struct_0 @ sk_A)
% 3.58/3.78        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 3.58/3.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 3.58/3.78      inference('demod', [status(thm)], ['39', '40'])).
% 3.58/3.78  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 3.58/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.58/3.78  thf('43', plain,
% 3.58/3.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ (sk_B_1 @ sk_A)))),
% 3.58/3.78      inference('clc', [status(thm)], ['41', '42'])).
% 3.58/3.78  thf('44', plain,
% 3.58/3.78      (![X12 : $i]:
% 3.58/3.78         ((m1_subset_1 @ (sk_B_1 @ X12) @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 3.58/3.78          | ~ (l1_pre_topc @ X12)
% 3.58/3.78          | ~ (v2_pre_topc @ X12)
% 3.58/3.78          | (v2_struct_0 @ X12))),
% 3.58/3.78      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 3.58/3.78  thf(cc1_subset_1, axiom,
% 3.58/3.78    (![A:$i]:
% 3.58/3.78     ( ( v1_xboole_0 @ A ) =>
% 3.58/3.78       ( ![B:$i]:
% 3.58/3.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.58/3.78  thf('45', plain,
% 3.58/3.78      (![X7 : $i, X8 : $i]:
% 3.58/3.78         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 3.58/3.78          | (v1_xboole_0 @ X7)
% 3.58/3.78          | ~ (v1_xboole_0 @ X8))),
% 3.58/3.78      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.58/3.78  thf('46', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((v2_struct_0 @ X0)
% 3.58/3.78          | ~ (v2_pre_topc @ X0)
% 3.58/3.78          | ~ (l1_pre_topc @ X0)
% 3.58/3.78          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 3.58/3.78          | (v1_xboole_0 @ (sk_B_1 @ X0)))),
% 3.58/3.78      inference('sup-', [status(thm)], ['44', '45'])).
% 3.58/3.78  thf('47', plain,
% 3.58/3.78      (((v1_xboole_0 @ (sk_B_1 @ sk_A))
% 3.58/3.78        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 3.58/3.78        | ~ (l1_pre_topc @ sk_A)
% 3.58/3.78        | ~ (v2_pre_topc @ sk_A)
% 3.58/3.78        | (v2_struct_0 @ sk_A))),
% 3.58/3.78      inference('sup-', [status(thm)], ['43', '46'])).
% 3.58/3.78  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 3.58/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.58/3.78  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 3.58/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.58/3.78  thf('50', plain,
% 3.58/3.78      (((v1_xboole_0 @ (sk_B_1 @ sk_A))
% 3.58/3.78        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 3.58/3.78        | (v2_struct_0 @ sk_A))),
% 3.58/3.78      inference('demod', [status(thm)], ['47', '48', '49'])).
% 3.58/3.78  thf('51', plain, (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (sk_B_1 @ sk_A)))),
% 3.58/3.78      inference('simplify', [status(thm)], ['50'])).
% 3.58/3.78  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 3.58/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.58/3.78  thf('53', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 3.58/3.78      inference('clc', [status(thm)], ['51', '52'])).
% 3.58/3.78  thf('54', plain,
% 3.58/3.78      (![X12 : $i]:
% 3.58/3.78         (~ (v1_xboole_0 @ (sk_B_1 @ X12))
% 3.58/3.78          | ~ (l1_pre_topc @ X12)
% 3.58/3.78          | ~ (v2_pre_topc @ X12)
% 3.58/3.78          | (v2_struct_0 @ X12))),
% 3.58/3.78      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 3.58/3.78  thf('55', plain,
% 3.58/3.78      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 3.58/3.78      inference('sup-', [status(thm)], ['53', '54'])).
% 3.58/3.78  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 3.58/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.58/3.78  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 3.58/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.58/3.78  thf('58', plain, ((v2_struct_0 @ sk_A)),
% 3.58/3.78      inference('demod', [status(thm)], ['55', '56', '57'])).
% 3.58/3.78  thf('59', plain, ($false), inference('demod', [status(thm)], ['0', '58'])).
% 3.58/3.78  
% 3.58/3.78  % SZS output end Refutation
% 3.58/3.78  
% 3.58/3.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
