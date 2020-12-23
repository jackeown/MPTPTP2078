%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fp8URI6k7p

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:04 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 137 expanded)
%              Number of leaves         :   35 (  56 expanded)
%              Depth                    :   19
%              Number of atoms          :  646 (1119 expanded)
%              Number of equality atoms :   45 (  60 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['1','4'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X22 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
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

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_tex_2 @ X19 @ X20 )
      | ~ ( v2_tex_2 @ X21 @ X20 )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( X19 = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ X5 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['41','42'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fp8URI6k7p
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.80  % Solved by: fo/fo7.sh
% 0.60/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.80  % done 458 iterations in 0.348s
% 0.60/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.80  % SZS output start Refutation
% 0.60/0.80  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.60/0.80  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.60/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.80  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.60/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.80  thf(sk_B_type, type, sk_B: $i > $i).
% 0.60/0.80  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.80  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.60/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.60/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.80  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.60/0.80  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.60/0.80  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.60/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.80  thf(t46_tex_2, conjecture,
% 0.60/0.80    (![A:$i]:
% 0.60/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.80       ( ![B:$i]:
% 0.60/0.80         ( ( ( v1_xboole_0 @ B ) & 
% 0.60/0.80             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.80           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.60/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.80    (~( ![A:$i]:
% 0.60/0.80        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.60/0.80            ( l1_pre_topc @ A ) ) =>
% 0.60/0.80          ( ![B:$i]:
% 0.60/0.80            ( ( ( v1_xboole_0 @ B ) & 
% 0.60/0.80                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.80              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.60/0.80    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.60/0.80  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('1', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('2', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf(l13_xboole_0, axiom,
% 0.60/0.80    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.60/0.80  thf('3', plain,
% 0.60/0.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.80  thf('4', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.80  thf('5', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.60/0.80      inference('demod', [status(thm)], ['1', '4'])).
% 0.60/0.80  thf(t7_xboole_0, axiom,
% 0.60/0.80    (![A:$i]:
% 0.60/0.80     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.60/0.80          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.60/0.80  thf('6', plain,
% 0.60/0.80      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.60/0.80      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.60/0.80  thf(t1_subset, axiom,
% 0.60/0.80    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.60/0.80  thf('7', plain,
% 0.60/0.80      (![X9 : $i, X10 : $i]:
% 0.60/0.80         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.60/0.80      inference('cnf', [status(esa)], [t1_subset])).
% 0.60/0.80  thf('8', plain,
% 0.60/0.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.80  thf(redefinition_k6_domain_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.60/0.80       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.60/0.80  thf('9', plain,
% 0.60/0.80      (![X17 : $i, X18 : $i]:
% 0.60/0.80         ((v1_xboole_0 @ X17)
% 0.60/0.80          | ~ (m1_subset_1 @ X18 @ X17)
% 0.60/0.80          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.60/0.80      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.60/0.80  thf('10', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (((X0) = (k1_xboole_0))
% 0.60/0.80          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.60/0.80          | (v1_xboole_0 @ X0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['8', '9'])).
% 0.60/0.80  thf('11', plain,
% 0.60/0.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.80  thf('12', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.60/0.80          | ((X0) = (k1_xboole_0)))),
% 0.60/0.80      inference('clc', [status(thm)], ['10', '11'])).
% 0.60/0.80  thf('13', plain,
% 0.60/0.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.80  thf(t36_tex_2, axiom,
% 0.60/0.80    (![A:$i]:
% 0.60/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.80       ( ![B:$i]:
% 0.60/0.80         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.80           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.60/0.80  thf('14', plain,
% 0.60/0.80      (![X22 : $i, X23 : $i]:
% 0.60/0.80         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.60/0.80          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X22) @ X23)
% 0.60/0.80          | ~ (l1_pre_topc @ X23)
% 0.60/0.80          | ~ (v2_pre_topc @ X23)
% 0.60/0.80          | (v2_struct_0 @ X23))),
% 0.60/0.80      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.60/0.80  thf('15', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 0.60/0.80          | (v2_struct_0 @ X0)
% 0.60/0.80          | ~ (v2_pre_topc @ X0)
% 0.60/0.80          | ~ (l1_pre_topc @ X0)
% 0.60/0.80          | (v2_tex_2 @ 
% 0.60/0.80             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.60/0.80             X0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['13', '14'])).
% 0.60/0.80  thf('16', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.60/0.80          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 0.60/0.80          | ~ (l1_pre_topc @ X0)
% 0.60/0.80          | ~ (v2_pre_topc @ X0)
% 0.60/0.80          | (v2_struct_0 @ X0)
% 0.60/0.80          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['12', '15'])).
% 0.60/0.80  thf('17', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((v2_struct_0 @ X0)
% 0.60/0.80          | ~ (v2_pre_topc @ X0)
% 0.60/0.80          | ~ (l1_pre_topc @ X0)
% 0.60/0.80          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 0.60/0.80          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 0.60/0.80      inference('simplify', [status(thm)], ['16'])).
% 0.60/0.80  thf('18', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.60/0.80          | ((X0) = (k1_xboole_0)))),
% 0.60/0.80      inference('clc', [status(thm)], ['10', '11'])).
% 0.60/0.80  thf('19', plain,
% 0.60/0.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.80  thf(dt_k6_domain_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.60/0.80       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.60/0.80  thf('20', plain,
% 0.60/0.80      (![X15 : $i, X16 : $i]:
% 0.60/0.80         ((v1_xboole_0 @ X15)
% 0.60/0.80          | ~ (m1_subset_1 @ X16 @ X15)
% 0.60/0.80          | (m1_subset_1 @ (k6_domain_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15)))),
% 0.60/0.80      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.60/0.80  thf('21', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (((X0) = (k1_xboole_0))
% 0.60/0.80          | (m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ 
% 0.60/0.80             (k1_zfmisc_1 @ X0))
% 0.60/0.80          | (v1_xboole_0 @ X0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['19', '20'])).
% 0.60/0.80  thf('22', plain,
% 0.60/0.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.80  thf('23', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.60/0.80          | ((X0) = (k1_xboole_0)))),
% 0.60/0.80      inference('clc', [status(thm)], ['21', '22'])).
% 0.60/0.80  thf('24', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.60/0.80          | ((X0) = (k1_xboole_0))
% 0.60/0.80          | ((X0) = (k1_xboole_0)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['18', '23'])).
% 0.60/0.80  thf('25', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (((X0) = (k1_xboole_0))
% 0.60/0.80          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.60/0.80      inference('simplify', [status(thm)], ['24'])).
% 0.60/0.80  thf(t4_subset_1, axiom,
% 0.60/0.80    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.60/0.80  thf('26', plain,
% 0.60/0.80      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.60/0.80      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.80  thf(d7_tex_2, axiom,
% 0.60/0.80    (![A:$i]:
% 0.60/0.80     ( ( l1_pre_topc @ A ) =>
% 0.60/0.80       ( ![B:$i]:
% 0.60/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.80           ( ( v3_tex_2 @ B @ A ) <=>
% 0.60/0.80             ( ( v2_tex_2 @ B @ A ) & 
% 0.60/0.80               ( ![C:$i]:
% 0.60/0.80                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.80                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.60/0.80                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.80  thf('27', plain,
% 0.60/0.80      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.80         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.60/0.80          | ~ (v3_tex_2 @ X19 @ X20)
% 0.60/0.80          | ~ (v2_tex_2 @ X21 @ X20)
% 0.60/0.80          | ~ (r1_tarski @ X19 @ X21)
% 0.60/0.80          | ((X19) = (X21))
% 0.60/0.80          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.60/0.80          | ~ (l1_pre_topc @ X20))),
% 0.60/0.80      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.60/0.80  thf('28', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         (~ (l1_pre_topc @ X0)
% 0.60/0.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.60/0.80          | ((k1_xboole_0) = (X1))
% 0.60/0.80          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.60/0.80          | ~ (v2_tex_2 @ X1 @ X0)
% 0.60/0.80          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['26', '27'])).
% 0.60/0.80  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.60/0.80  thf('29', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.60/0.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.60/0.80  thf('30', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         (~ (l1_pre_topc @ X0)
% 0.60/0.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.60/0.80          | ((k1_xboole_0) = (X1))
% 0.60/0.80          | ~ (v2_tex_2 @ X1 @ X0)
% 0.60/0.80          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.60/0.80      inference('demod', [status(thm)], ['28', '29'])).
% 0.60/0.80  thf('31', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 0.60/0.80          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.80          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.60/0.80          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.60/0.80          | ~ (l1_pre_topc @ X0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['25', '30'])).
% 0.60/0.80  thf(t1_boole, axiom,
% 0.60/0.80    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.60/0.80  thf('32', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.60/0.80      inference('cnf', [status(esa)], [t1_boole])).
% 0.60/0.80  thf(t49_zfmisc_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.60/0.80  thf('33', plain,
% 0.60/0.80      (![X4 : $i, X5 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ (k1_tarski @ X4) @ X5) != (k1_xboole_0))),
% 0.60/0.80      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.60/0.80  thf('34', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['32', '33'])).
% 0.60/0.80  thf('35', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 0.60/0.80          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.80          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.60/0.80          | ~ (l1_pre_topc @ X0))),
% 0.60/0.80      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 0.60/0.80  thf('36', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 0.60/0.80          | ~ (l1_pre_topc @ X0)
% 0.60/0.80          | ~ (v2_pre_topc @ X0)
% 0.60/0.80          | (v2_struct_0 @ X0)
% 0.60/0.80          | ~ (l1_pre_topc @ X0)
% 0.60/0.80          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.80          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['17', '35'])).
% 0.60/0.80  thf('37', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.80          | (v2_struct_0 @ X0)
% 0.60/0.80          | ~ (v2_pre_topc @ X0)
% 0.60/0.80          | ~ (l1_pre_topc @ X0)
% 0.60/0.80          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 0.60/0.80      inference('simplify', [status(thm)], ['36'])).
% 0.60/0.80  thf('38', plain,
% 0.60/0.80      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.60/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.80        | (v2_struct_0 @ sk_A))),
% 0.60/0.80      inference('sup-', [status(thm)], ['5', '37'])).
% 0.60/0.80  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('41', plain,
% 0.60/0.80      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 0.60/0.80      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.60/0.80  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('43', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.60/0.80      inference('clc', [status(thm)], ['41', '42'])).
% 0.60/0.80  thf(rc7_pre_topc, axiom,
% 0.60/0.80    (![A:$i]:
% 0.60/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.80       ( ?[B:$i]:
% 0.60/0.80         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.60/0.80           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.60/0.80  thf('44', plain,
% 0.60/0.80      (![X14 : $i]:
% 0.60/0.80         ((m1_subset_1 @ (sk_B_1 @ X14) @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.60/0.80          | ~ (l1_pre_topc @ X14)
% 0.60/0.80          | ~ (v2_pre_topc @ X14)
% 0.60/0.80          | (v2_struct_0 @ X14))),
% 0.60/0.80      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.60/0.80  thf(cc1_subset_1, axiom,
% 0.60/0.80    (![A:$i]:
% 0.60/0.80     ( ( v1_xboole_0 @ A ) =>
% 0.60/0.80       ( ![B:$i]:
% 0.60/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.60/0.80  thf('45', plain,
% 0.60/0.80      (![X7 : $i, X8 : $i]:
% 0.60/0.80         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.60/0.80          | (v1_xboole_0 @ X7)
% 0.60/0.80          | ~ (v1_xboole_0 @ X8))),
% 0.60/0.80      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.60/0.80  thf('46', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((v2_struct_0 @ X0)
% 0.60/0.80          | ~ (v2_pre_topc @ X0)
% 0.60/0.80          | ~ (l1_pre_topc @ X0)
% 0.60/0.80          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.60/0.80          | (v1_xboole_0 @ (sk_B_1 @ X0)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['44', '45'])).
% 0.60/0.80  thf('47', plain,
% 0.60/0.80      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.60/0.80        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.60/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.80        | (v2_struct_0 @ sk_A))),
% 0.60/0.80      inference('sup-', [status(thm)], ['43', '46'])).
% 0.60/0.80  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.60/0.80  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.80  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('51', plain, (((v1_xboole_0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.60/0.80      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.60/0.80  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('53', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 0.60/0.80      inference('clc', [status(thm)], ['51', '52'])).
% 0.60/0.80  thf('54', plain,
% 0.60/0.80      (![X14 : $i]:
% 0.60/0.80         (~ (v1_xboole_0 @ (sk_B_1 @ X14))
% 0.60/0.80          | ~ (l1_pre_topc @ X14)
% 0.60/0.80          | ~ (v2_pre_topc @ X14)
% 0.60/0.80          | (v2_struct_0 @ X14))),
% 0.60/0.80      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.60/0.80  thf('55', plain,
% 0.60/0.80      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.60/0.80      inference('sup-', [status(thm)], ['53', '54'])).
% 0.60/0.80  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('58', plain, ((v2_struct_0 @ sk_A)),
% 0.60/0.80      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.60/0.80  thf('59', plain, ($false), inference('demod', [status(thm)], ['0', '58'])).
% 0.60/0.80  
% 0.60/0.80  % SZS output end Refutation
% 0.60/0.80  
% 0.67/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
