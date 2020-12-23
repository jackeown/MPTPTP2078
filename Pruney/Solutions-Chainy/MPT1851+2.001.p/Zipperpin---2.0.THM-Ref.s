%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8PVEC3bY3E

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:59 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 523 expanded)
%              Number of leaves         :   30 ( 162 expanded)
%              Depth                    :   23
%              Number of atoms          : 1301 (5976 expanded)
%              Number of equality atoms :   24 ( 188 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(d2_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_tdlat_3 @ A )
      <=> ( ( u1_pre_topc @ A )
          = ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X29: $i] :
      ( ~ ( v2_tdlat_3 @ X29 )
      | ( ( u1_pre_topc @ X29 )
        = ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d2_tdlat_3])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( m1_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t18_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
              & ( v2_tdlat_3 @ A ) )
           => ( v2_tdlat_3 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                & ( v2_tdlat_3 @ A ) )
             => ( v2_tdlat_3 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_tex_2])).

thf('5',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( m1_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('20',plain,(
    ! [X28: $i] :
      ( ~ ( v2_tdlat_3 @ X28 )
      | ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc2_tdlat_3])).

thf('21',plain,
    ( ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('26',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( m1_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18','23','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['30','31'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_A @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X6: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('41',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t58_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
       => ( v2_pre_topc @ A ) ) ) )).

thf('42',plain,(
    ! [X7: $i] :
      ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t58_pre_topc])).

thf('43',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v2_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(demod,[status(thm)],['21','22'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf('51',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','49','50'])).

thf('52',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','51'])).

thf('53',plain,(
    ! [X29: $i] :
      ( ( ( u1_pre_topc @ X29 )
       != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ X29 ) ) )
      | ( v2_tdlat_3 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d2_tdlat_3])).

thf('54',plain,
    ( ( ( u1_pre_topc @ sk_B )
     != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_tdlat_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('56',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t31_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_2])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_tops_2 @ X19 @ X20 )
      | ( r1_tarski @ X19 @ ( u1_pre_topc @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('68',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf(t35_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v1_tops_2 @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) )
                   => ( ( D = B )
                     => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_tops_2 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ( v1_tops_2 @ X17 @ X18 )
      | ( X17 != X15 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_2])).

thf('70',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ( v1_tops_2 @ X15 @ X18 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_tops_2 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['30','31'])).

thf('76',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf('77',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( m1_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( m1_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_pre_topc @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('88',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( r1_tarski @ X19 @ ( u1_pre_topc @ X20 ) )
      | ( v1_tops_2 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['93','94','96'])).

thf('98',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['72','73','74','75','97'])).

thf('99',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['66','98'])).

thf('100',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('101',plain,
    ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_B )
      = ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['30','31'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('104',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_tops_2 @ X19 @ X20 )
      | ( r1_tarski @ X19 @ ( u1_pre_topc @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('109',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('113',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('114',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ( v1_tops_2 @ X15 @ X18 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_tops_2 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_A @ sk_B )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf('120',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('122',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('124',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( r1_tarski @ X19 @ ( u1_pre_topc @ X20 ) )
      | ( v1_tops_2 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('129',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_B )
    | ~ ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('132',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['116','117','118','119','132'])).

thf('134',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['111','133'])).

thf('135',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['101','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tdlat_3 @ sk_B ) ),
    inference(demod,[status(thm)],['54','135','136'])).

thf('138',plain,(
    ~ ( v2_tdlat_3 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ( u1_pre_topc @ sk_A )
 != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','139'])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ( u1_pre_topc @ sk_A )
 != ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    $false ),
    inference(simplify,[status(thm)],['143'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8PVEC3bY3E
% 0.12/0.31  % Computer   : n013.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 11:43:40 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.32  % Python version: Python 3.6.8
% 0.12/0.32  % Running in FO mode
% 0.17/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.17/0.51  % Solved by: fo/fo7.sh
% 0.17/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.17/0.51  % done 119 iterations in 0.076s
% 0.17/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.17/0.51  % SZS output start Refutation
% 0.17/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.17/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.17/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.17/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.17/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.17/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.17/0.51  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.17/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.17/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.17/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.17/0.51  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.17/0.51  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.17/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.17/0.51  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.17/0.51  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.17/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.17/0.51  thf(d2_tdlat_3, axiom,
% 0.17/0.51    (![A:$i]:
% 0.17/0.51     ( ( l1_pre_topc @ A ) =>
% 0.17/0.51       ( ( v2_tdlat_3 @ A ) <=>
% 0.17/0.51         ( ( u1_pre_topc @ A ) =
% 0.17/0.51           ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.17/0.51  thf('0', plain,
% 0.17/0.51      (![X29 : $i]:
% 0.17/0.51         (~ (v2_tdlat_3 @ X29)
% 0.17/0.51          | ((u1_pre_topc @ X29)
% 0.17/0.51              = (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ X29)))
% 0.17/0.51          | ~ (l1_pre_topc @ X29))),
% 0.17/0.51      inference('cnf', [status(esa)], [d2_tdlat_3])).
% 0.17/0.51  thf(t2_tsep_1, axiom,
% 0.17/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.17/0.51  thf('1', plain,
% 0.17/0.51      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.17/0.51      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.17/0.51  thf(t65_pre_topc, axiom,
% 0.17/0.51    (![A:$i]:
% 0.17/0.51     ( ( l1_pre_topc @ A ) =>
% 0.17/0.51       ( ![B:$i]:
% 0.17/0.51         ( ( l1_pre_topc @ B ) =>
% 0.17/0.51           ( ( m1_pre_topc @ A @ B ) <=>
% 0.17/0.51             ( m1_pre_topc @
% 0.17/0.51               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.17/0.51  thf('2', plain,
% 0.17/0.51      (![X10 : $i, X11 : $i]:
% 0.17/0.51         (~ (l1_pre_topc @ X10)
% 0.17/0.51          | ~ (m1_pre_topc @ X11 @ X10)
% 0.17/0.51          | (m1_pre_topc @ X11 @ 
% 0.17/0.51             (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.17/0.51          | ~ (l1_pre_topc @ X11))),
% 0.17/0.51      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.17/0.51  thf('3', plain,
% 0.17/0.51      (![X0 : $i]:
% 0.17/0.51         (~ (l1_pre_topc @ X0)
% 0.17/0.51          | ~ (l1_pre_topc @ X0)
% 0.17/0.51          | (m1_pre_topc @ X0 @ 
% 0.17/0.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.17/0.51          | ~ (l1_pre_topc @ X0))),
% 0.17/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.17/0.51  thf('4', plain,
% 0.17/0.51      (![X0 : $i]:
% 0.17/0.51         ((m1_pre_topc @ X0 @ 
% 0.17/0.51           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.17/0.51          | ~ (l1_pre_topc @ X0))),
% 0.17/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.17/0.51  thf(t18_tex_2, conjecture,
% 0.17/0.51    (![A:$i]:
% 0.17/0.51     ( ( l1_pre_topc @ A ) =>
% 0.17/0.51       ( ![B:$i]:
% 0.17/0.51         ( ( l1_pre_topc @ B ) =>
% 0.17/0.51           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.17/0.51                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.17/0.51               ( v2_tdlat_3 @ A ) ) =>
% 0.17/0.51             ( v2_tdlat_3 @ B ) ) ) ) ))).
% 0.17/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.17/0.51    (~( ![A:$i]:
% 0.17/0.51        ( ( l1_pre_topc @ A ) =>
% 0.17/0.51          ( ![B:$i]:
% 0.17/0.51            ( ( l1_pre_topc @ B ) =>
% 0.17/0.51              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.17/0.51                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.17/0.51                  ( v2_tdlat_3 @ A ) ) =>
% 0.17/0.51                ( v2_tdlat_3 @ B ) ) ) ) ) )),
% 0.17/0.51    inference('cnf.neg', [status(esa)], [t18_tex_2])).
% 0.17/0.51  thf('5', plain,
% 0.17/0.51      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.17/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf(t59_pre_topc, axiom,
% 0.17/0.51    (![A:$i]:
% 0.17/0.51     ( ( l1_pre_topc @ A ) =>
% 0.17/0.51       ( ![B:$i]:
% 0.17/0.51         ( ( m1_pre_topc @
% 0.17/0.51             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.17/0.51           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.17/0.51  thf('6', plain,
% 0.17/0.51      (![X8 : $i, X9 : $i]:
% 0.17/0.51         (~ (m1_pre_topc @ X8 @ 
% 0.17/0.51             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.17/0.51          | (m1_pre_topc @ X8 @ X9)
% 0.17/0.51          | ~ (l1_pre_topc @ X9))),
% 0.17/0.51      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.17/0.51  thf('7', plain,
% 0.17/0.51      (![X0 : $i]:
% 0.17/0.51         (~ (m1_pre_topc @ X0 @ 
% 0.17/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.17/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.17/0.51          | (m1_pre_topc @ X0 @ sk_B))),
% 0.17/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.17/0.51  thf('8', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('9', plain,
% 0.17/0.51      (![X0 : $i]:
% 0.17/0.51         (~ (m1_pre_topc @ X0 @ 
% 0.17/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.17/0.51          | (m1_pre_topc @ X0 @ sk_B))),
% 0.17/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.17/0.51  thf('10', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_B))),
% 0.17/0.51      inference('sup-', [status(thm)], ['4', '9'])).
% 0.17/0.51  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('12', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.17/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.17/0.51  thf('13', plain,
% 0.17/0.51      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.17/0.51      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.17/0.51  thf(t4_tsep_1, axiom,
% 0.17/0.51    (![A:$i]:
% 0.17/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.17/0.51       ( ![B:$i]:
% 0.17/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.17/0.51           ( ![C:$i]:
% 0.17/0.51             ( ( m1_pre_topc @ C @ A ) =>
% 0.17/0.51               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.17/0.51                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.17/0.51  thf('14', plain,
% 0.17/0.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.17/0.51         (~ (m1_pre_topc @ X22 @ X23)
% 0.17/0.51          | ~ (m1_pre_topc @ X22 @ X24)
% 0.17/0.51          | (r1_tarski @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X24))
% 0.17/0.51          | ~ (m1_pre_topc @ X24 @ X23)
% 0.17/0.51          | ~ (l1_pre_topc @ X23)
% 0.17/0.51          | ~ (v2_pre_topc @ X23))),
% 0.17/0.51      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.17/0.51  thf('15', plain,
% 0.17/0.51      (![X0 : $i, X1 : $i]:
% 0.17/0.51         (~ (l1_pre_topc @ X0)
% 0.17/0.51          | ~ (v2_pre_topc @ X0)
% 0.17/0.51          | ~ (l1_pre_topc @ X0)
% 0.17/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.17/0.51          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.17/0.51          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.17/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.17/0.51  thf('16', plain,
% 0.17/0.51      (![X0 : $i, X1 : $i]:
% 0.17/0.51         (~ (m1_pre_topc @ X0 @ X1)
% 0.17/0.51          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.17/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.17/0.51          | ~ (v2_pre_topc @ X0)
% 0.17/0.51          | ~ (l1_pre_topc @ X0))),
% 0.17/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.17/0.51  thf('17', plain,
% 0.17/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.17/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.17/0.51        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.17/0.51        | (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.17/0.51      inference('sup-', [status(thm)], ['12', '16'])).
% 0.17/0.51  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf(cc2_tdlat_3, axiom,
% 0.17/0.51    (![A:$i]:
% 0.17/0.51     ( ( l1_pre_topc @ A ) => ( ( v2_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.17/0.51  thf('20', plain,
% 0.17/0.51      (![X28 : $i]:
% 0.17/0.51         (~ (v2_tdlat_3 @ X28) | (v2_pre_topc @ X28) | ~ (l1_pre_topc @ X28))),
% 0.17/0.51      inference('cnf', [status(esa)], [cc2_tdlat_3])).
% 0.17/0.51  thf('21', plain, (((v2_pre_topc @ sk_A) | ~ (v2_tdlat_3 @ sk_A))),
% 0.17/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.17/0.51  thf('22', plain, ((v2_tdlat_3 @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.17/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.17/0.51  thf('24', plain,
% 0.17/0.51      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.17/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('25', plain,
% 0.17/0.51      (![X0 : $i]:
% 0.17/0.51         ((m1_pre_topc @ X0 @ 
% 0.17/0.51           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.17/0.51          | ~ (l1_pre_topc @ X0))),
% 0.17/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.17/0.51  thf('26', plain,
% 0.17/0.51      (((m1_pre_topc @ sk_B @ 
% 0.17/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.17/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.17/0.51      inference('sup+', [status(thm)], ['24', '25'])).
% 0.17/0.51  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('28', plain,
% 0.17/0.51      ((m1_pre_topc @ sk_B @ 
% 0.17/0.51        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.17/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.17/0.51  thf('29', plain,
% 0.17/0.51      (![X8 : $i, X9 : $i]:
% 0.17/0.51         (~ (m1_pre_topc @ X8 @ 
% 0.17/0.51             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.17/0.51          | (m1_pre_topc @ X8 @ X9)
% 0.17/0.51          | ~ (l1_pre_topc @ X9))),
% 0.17/0.51      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.17/0.51  thf('30', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.17/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.17/0.51  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('32', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.17/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.17/0.51  thf('33', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.17/0.51      inference('demod', [status(thm)], ['17', '18', '23', '32'])).
% 0.17/0.51  thf(d10_xboole_0, axiom,
% 0.17/0.51    (![A:$i,B:$i]:
% 0.17/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.17/0.51  thf('34', plain,
% 0.17/0.51      (![X0 : $i, X2 : $i]:
% 0.17/0.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.17/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.17/0.51  thf('35', plain,
% 0.17/0.51      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.17/0.51        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A)))),
% 0.17/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.17/0.51  thf('36', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.17/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.17/0.51  thf('37', plain,
% 0.17/0.51      (![X0 : $i, X1 : $i]:
% 0.17/0.51         (~ (m1_pre_topc @ X0 @ X1)
% 0.17/0.51          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.17/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.17/0.51          | ~ (v2_pre_topc @ X0)
% 0.17/0.51          | ~ (l1_pre_topc @ X0))),
% 0.17/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.17/0.51  thf('38', plain,
% 0.17/0.51      ((~ (l1_pre_topc @ sk_B)
% 0.17/0.51        | ~ (v2_pre_topc @ sk_B)
% 0.17/0.51        | ~ (m1_pre_topc @ sk_A @ sk_B)
% 0.17/0.51        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.17/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.17/0.51  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf(fc6_pre_topc, axiom,
% 0.17/0.51    (![A:$i]:
% 0.17/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.17/0.51       ( ( v1_pre_topc @
% 0.17/0.51           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.17/0.51         ( v2_pre_topc @
% 0.17/0.51           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.17/0.51  thf('40', plain,
% 0.17/0.51      (![X6 : $i]:
% 0.17/0.51         ((v2_pre_topc @ 
% 0.17/0.51           (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.17/0.51          | ~ (l1_pre_topc @ X6)
% 0.17/0.51          | ~ (v2_pre_topc @ X6))),
% 0.17/0.51      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.17/0.51  thf('41', plain,
% 0.17/0.51      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.17/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf(t58_pre_topc, axiom,
% 0.17/0.51    (![A:$i]:
% 0.17/0.51     ( ( l1_pre_topc @ A ) =>
% 0.17/0.51       ( ( v2_pre_topc @
% 0.17/0.51           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.17/0.51         ( v2_pre_topc @ A ) ) ))).
% 0.17/0.51  thf('42', plain,
% 0.17/0.51      (![X7 : $i]:
% 0.17/0.51         (~ (v2_pre_topc @ 
% 0.17/0.51             (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.17/0.51          | (v2_pre_topc @ X7)
% 0.17/0.51          | ~ (l1_pre_topc @ X7))),
% 0.17/0.51      inference('cnf', [status(esa)], [t58_pre_topc])).
% 0.17/0.51  thf('43', plain,
% 0.17/0.51      ((~ (v2_pre_topc @ 
% 0.17/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.17/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.17/0.51        | (v2_pre_topc @ sk_B))),
% 0.17/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.17/0.51  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('45', plain,
% 0.17/0.51      ((~ (v2_pre_topc @ 
% 0.17/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.17/0.51        | (v2_pre_topc @ sk_B))),
% 0.17/0.51      inference('demod', [status(thm)], ['43', '44'])).
% 0.17/0.51  thf('46', plain,
% 0.17/0.51      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 0.17/0.51      inference('sup-', [status(thm)], ['40', '45'])).
% 0.17/0.51  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.17/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.17/0.51  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('49', plain, ((v2_pre_topc @ sk_B)),
% 0.17/0.51      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.17/0.51  thf('50', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.17/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.17/0.51  thf('51', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.17/0.51      inference('demod', [status(thm)], ['38', '39', '49', '50'])).
% 0.17/0.51  thf('52', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.17/0.51      inference('demod', [status(thm)], ['35', '51'])).
% 0.17/0.51  thf('53', plain,
% 0.17/0.51      (![X29 : $i]:
% 0.17/0.51         (((u1_pre_topc @ X29)
% 0.17/0.51            != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ X29)))
% 0.17/0.51          | (v2_tdlat_3 @ X29)
% 0.17/0.51          | ~ (l1_pre_topc @ X29))),
% 0.17/0.51      inference('cnf', [status(esa)], [d2_tdlat_3])).
% 0.17/0.51  thf('54', plain,
% 0.17/0.51      ((((u1_pre_topc @ sk_B)
% 0.17/0.51          != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.17/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.17/0.51        | (v2_tdlat_3 @ sk_B))),
% 0.17/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.17/0.51  thf('55', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.17/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.17/0.51  thf(dt_u1_pre_topc, axiom,
% 0.17/0.51    (![A:$i]:
% 0.17/0.51     ( ( l1_pre_topc @ A ) =>
% 0.17/0.51       ( m1_subset_1 @
% 0.17/0.51         ( u1_pre_topc @ A ) @ 
% 0.17/0.51         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.17/0.51  thf('56', plain,
% 0.17/0.51      (![X5 : $i]:
% 0.17/0.51         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.17/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.17/0.51          | ~ (l1_pre_topc @ X5))),
% 0.17/0.51      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.17/0.51  thf(t31_tops_2, axiom,
% 0.17/0.51    (![A:$i]:
% 0.17/0.51     ( ( l1_pre_topc @ A ) =>
% 0.17/0.51       ( ![B:$i]:
% 0.17/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.17/0.51           ( ![C:$i]:
% 0.17/0.51             ( ( m1_subset_1 @
% 0.17/0.51                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.17/0.51               ( m1_subset_1 @
% 0.17/0.51                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.17/0.51  thf('57', plain,
% 0.17/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.17/0.51         (~ (m1_pre_topc @ X12 @ X13)
% 0.17/0.51          | (m1_subset_1 @ X14 @ 
% 0.17/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.17/0.51          | ~ (m1_subset_1 @ X14 @ 
% 0.17/0.51               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.17/0.51          | ~ (l1_pre_topc @ X13))),
% 0.17/0.51      inference('cnf', [status(esa)], [t31_tops_2])).
% 0.17/0.51  thf('58', plain,
% 0.17/0.51      (![X0 : $i, X1 : $i]:
% 0.17/0.51         (~ (l1_pre_topc @ X0)
% 0.17/0.51          | ~ (l1_pre_topc @ X1)
% 0.17/0.51          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.17/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.17/0.51          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.17/0.51      inference('sup-', [status(thm)], ['56', '57'])).
% 0.17/0.51  thf('59', plain,
% 0.17/0.51      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.17/0.51         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.17/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.17/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.17/0.51      inference('sup-', [status(thm)], ['55', '58'])).
% 0.17/0.51  thf('60', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('62', plain,
% 0.17/0.51      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.17/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.17/0.51      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.17/0.51  thf(t78_tops_2, axiom,
% 0.17/0.51    (![A:$i]:
% 0.17/0.51     ( ( l1_pre_topc @ A ) =>
% 0.17/0.51       ( ![B:$i]:
% 0.17/0.51         ( ( m1_subset_1 @
% 0.17/0.51             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.17/0.51           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.17/0.51  thf('63', plain,
% 0.17/0.51      (![X19 : $i, X20 : $i]:
% 0.17/0.51         (~ (m1_subset_1 @ X19 @ 
% 0.17/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.17/0.51          | ~ (v1_tops_2 @ X19 @ X20)
% 0.17/0.51          | (r1_tarski @ X19 @ (u1_pre_topc @ X20))
% 0.17/0.51          | ~ (l1_pre_topc @ X20))),
% 0.17/0.51      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.17/0.51  thf('64', plain,
% 0.17/0.51      ((~ (l1_pre_topc @ sk_B)
% 0.17/0.51        | (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B))
% 0.17/0.51        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B))),
% 0.17/0.51      inference('sup-', [status(thm)], ['62', '63'])).
% 0.17/0.51  thf('65', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('66', plain,
% 0.17/0.51      (((r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B))
% 0.17/0.51        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B))),
% 0.17/0.51      inference('demod', [status(thm)], ['64', '65'])).
% 0.17/0.51  thf('67', plain,
% 0.17/0.51      (![X5 : $i]:
% 0.17/0.51         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.17/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.17/0.51          | ~ (l1_pre_topc @ X5))),
% 0.17/0.51      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.17/0.51  thf('68', plain,
% 0.17/0.51      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.17/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.17/0.51      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.17/0.51  thf(t35_tops_2, axiom,
% 0.17/0.51    (![A:$i]:
% 0.17/0.51     ( ( l1_pre_topc @ A ) =>
% 0.17/0.51       ( ![B:$i]:
% 0.17/0.51         ( ( m1_subset_1 @
% 0.17/0.51             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.17/0.51           ( ![C:$i]:
% 0.17/0.51             ( ( m1_pre_topc @ C @ A ) =>
% 0.17/0.51               ( ( v1_tops_2 @ B @ A ) =>
% 0.17/0.51                 ( ![D:$i]:
% 0.17/0.51                   ( ( m1_subset_1 @
% 0.17/0.51                       D @ 
% 0.17/0.51                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.17/0.51                     ( ( ( D ) = ( B ) ) => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.17/0.51  thf('69', plain,
% 0.17/0.51      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.17/0.51         (~ (m1_subset_1 @ X15 @ 
% 0.17/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.17/0.51          | ~ (v1_tops_2 @ X15 @ X16)
% 0.17/0.51          | ~ (m1_subset_1 @ X17 @ 
% 0.17/0.51               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.17/0.51          | (v1_tops_2 @ X17 @ X18)
% 0.17/0.51          | ((X17) != (X15))
% 0.17/0.51          | ~ (m1_pre_topc @ X18 @ X16)
% 0.17/0.51          | ~ (l1_pre_topc @ X16))),
% 0.17/0.51      inference('cnf', [status(esa)], [t35_tops_2])).
% 0.17/0.51  thf('70', plain,
% 0.17/0.51      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.17/0.51         (~ (l1_pre_topc @ X16)
% 0.17/0.51          | ~ (m1_pre_topc @ X18 @ X16)
% 0.17/0.51          | (v1_tops_2 @ X15 @ X18)
% 0.17/0.51          | ~ (m1_subset_1 @ X15 @ 
% 0.17/0.51               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.17/0.51          | ~ (v1_tops_2 @ X15 @ X16)
% 0.17/0.51          | ~ (m1_subset_1 @ X15 @ 
% 0.17/0.51               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))))),
% 0.17/0.51      inference('simplify', [status(thm)], ['69'])).
% 0.17/0.51  thf('71', plain,
% 0.17/0.51      (![X0 : $i]:
% 0.17/0.51         (~ (m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.17/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.17/0.51          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ X0)
% 0.17/0.51          | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)
% 0.17/0.51          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.17/0.51          | ~ (l1_pre_topc @ X0))),
% 0.17/0.51      inference('sup-', [status(thm)], ['68', '70'])).
% 0.17/0.51  thf('72', plain,
% 0.17/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.17/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.17/0.51        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.17/0.51        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)
% 0.17/0.51        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A))),
% 0.17/0.51      inference('sup-', [status(thm)], ['67', '71'])).
% 0.17/0.51  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('75', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.17/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.17/0.51  thf('76', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.17/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.17/0.51  thf('77', plain,
% 0.17/0.51      (![X10 : $i, X11 : $i]:
% 0.17/0.51         (~ (l1_pre_topc @ X10)
% 0.17/0.51          | ~ (m1_pre_topc @ X11 @ X10)
% 0.17/0.51          | (m1_pre_topc @ X11 @ 
% 0.17/0.51             (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.17/0.51          | ~ (l1_pre_topc @ X11))),
% 0.17/0.51      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.17/0.51  thf('78', plain,
% 0.17/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.17/0.51        | (m1_pre_topc @ sk_A @ 
% 0.17/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.17/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.17/0.51      inference('sup-', [status(thm)], ['76', '77'])).
% 0.17/0.51  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('80', plain,
% 0.17/0.51      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.17/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('81', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('82', plain,
% 0.17/0.51      ((m1_pre_topc @ sk_A @ 
% 0.17/0.51        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.17/0.51      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.17/0.51  thf('83', plain,
% 0.17/0.51      (![X8 : $i, X9 : $i]:
% 0.17/0.51         (~ (m1_pre_topc @ X8 @ 
% 0.17/0.51             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.17/0.51          | (m1_pre_topc @ X8 @ X9)
% 0.17/0.51          | ~ (l1_pre_topc @ X9))),
% 0.17/0.51      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.17/0.51  thf('84', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_A))),
% 0.17/0.51      inference('sup-', [status(thm)], ['82', '83'])).
% 0.17/0.51  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('86', plain, ((m1_pre_topc @ sk_A @ sk_A)),
% 0.17/0.51      inference('demod', [status(thm)], ['84', '85'])).
% 0.17/0.51  thf('87', plain,
% 0.17/0.51      (![X0 : $i, X1 : $i]:
% 0.17/0.51         (~ (l1_pre_topc @ X0)
% 0.17/0.51          | ~ (l1_pre_topc @ X1)
% 0.17/0.51          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.17/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.17/0.51          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.17/0.51      inference('sup-', [status(thm)], ['56', '57'])).
% 0.17/0.51  thf('88', plain,
% 0.17/0.51      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.17/0.51         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.17/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.17/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.17/0.51      inference('sup-', [status(thm)], ['86', '87'])).
% 0.17/0.51  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('91', plain,
% 0.17/0.51      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.17/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.17/0.51      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.17/0.51  thf('92', plain,
% 0.17/0.51      (![X19 : $i, X20 : $i]:
% 0.17/0.51         (~ (m1_subset_1 @ X19 @ 
% 0.17/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.17/0.51          | ~ (r1_tarski @ X19 @ (u1_pre_topc @ X20))
% 0.17/0.51          | (v1_tops_2 @ X19 @ X20)
% 0.17/0.51          | ~ (l1_pre_topc @ X20))),
% 0.17/0.51      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.17/0.51  thf('93', plain,
% 0.17/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.17/0.51        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.17/0.51        | ~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.17/0.51      inference('sup-', [status(thm)], ['91', '92'])).
% 0.17/0.51  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('95', plain,
% 0.17/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.17/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.17/0.51  thf('96', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.17/0.51      inference('simplify', [status(thm)], ['95'])).
% 0.17/0.51  thf('97', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 0.17/0.51      inference('demod', [status(thm)], ['93', '94', '96'])).
% 0.17/0.51  thf('98', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)),
% 0.17/0.51      inference('demod', [status(thm)], ['72', '73', '74', '75', '97'])).
% 0.17/0.51  thf('99', plain, ((r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B))),
% 0.17/0.51      inference('demod', [status(thm)], ['66', '98'])).
% 0.17/0.51  thf('100', plain,
% 0.17/0.51      (![X0 : $i, X2 : $i]:
% 0.17/0.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.17/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.17/0.51  thf('101', plain,
% 0.17/0.51      ((~ (r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.17/0.51        | ((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A)))),
% 0.17/0.51      inference('sup-', [status(thm)], ['99', '100'])).
% 0.17/0.51  thf('102', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.17/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.17/0.51  thf('103', plain,
% 0.17/0.51      (![X0 : $i, X1 : $i]:
% 0.17/0.51         (~ (l1_pre_topc @ X0)
% 0.17/0.51          | ~ (l1_pre_topc @ X1)
% 0.17/0.51          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.17/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.17/0.51          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.17/0.51      inference('sup-', [status(thm)], ['56', '57'])).
% 0.17/0.51  thf('104', plain,
% 0.17/0.51      (((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.17/0.51         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.17/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.17/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.17/0.51      inference('sup-', [status(thm)], ['102', '103'])).
% 0.17/0.51  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('106', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('107', plain,
% 0.17/0.51      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.17/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.17/0.51      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.17/0.51  thf('108', plain,
% 0.17/0.51      (![X19 : $i, X20 : $i]:
% 0.17/0.51         (~ (m1_subset_1 @ X19 @ 
% 0.17/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.17/0.51          | ~ (v1_tops_2 @ X19 @ X20)
% 0.17/0.51          | (r1_tarski @ X19 @ (u1_pre_topc @ X20))
% 0.17/0.51          | ~ (l1_pre_topc @ X20))),
% 0.17/0.51      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.17/0.51  thf('109', plain,
% 0.17/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.17/0.51        | (r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.17/0.51        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A))),
% 0.17/0.51      inference('sup-', [status(thm)], ['107', '108'])).
% 0.17/0.51  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('111', plain,
% 0.17/0.51      (((r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.17/0.51        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A))),
% 0.17/0.51      inference('demod', [status(thm)], ['109', '110'])).
% 0.17/0.51  thf('112', plain,
% 0.17/0.51      (![X5 : $i]:
% 0.17/0.51         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.17/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.17/0.51          | ~ (l1_pre_topc @ X5))),
% 0.17/0.51      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.17/0.51  thf('113', plain,
% 0.17/0.51      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.17/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.17/0.51      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.17/0.51  thf('114', plain,
% 0.17/0.51      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.17/0.51         (~ (l1_pre_topc @ X16)
% 0.17/0.51          | ~ (m1_pre_topc @ X18 @ X16)
% 0.17/0.51          | (v1_tops_2 @ X15 @ X18)
% 0.17/0.51          | ~ (m1_subset_1 @ X15 @ 
% 0.17/0.51               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.17/0.51          | ~ (v1_tops_2 @ X15 @ X16)
% 0.17/0.51          | ~ (m1_subset_1 @ X15 @ 
% 0.17/0.51               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))))),
% 0.17/0.51      inference('simplify', [status(thm)], ['69'])).
% 0.17/0.51  thf('115', plain,
% 0.17/0.51      (![X0 : $i]:
% 0.17/0.51         (~ (m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.17/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.17/0.51          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ X0)
% 0.17/0.51          | (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A)
% 0.17/0.51          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.17/0.51          | ~ (l1_pre_topc @ X0))),
% 0.17/0.51      inference('sup-', [status(thm)], ['113', '114'])).
% 0.17/0.51  thf('116', plain,
% 0.17/0.51      ((~ (l1_pre_topc @ sk_B)
% 0.17/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.17/0.51        | ~ (m1_pre_topc @ sk_A @ sk_B)
% 0.17/0.51        | (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A)
% 0.17/0.51        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_B))),
% 0.17/0.51      inference('sup-', [status(thm)], ['112', '115'])).
% 0.17/0.51  thf('117', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('118', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('119', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.17/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.17/0.51  thf('120', plain,
% 0.17/0.51      ((m1_pre_topc @ sk_B @ 
% 0.17/0.51        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.17/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.17/0.51  thf('121', plain,
% 0.17/0.51      (![X0 : $i]:
% 0.17/0.51         (~ (m1_pre_topc @ X0 @ 
% 0.17/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.17/0.51          | (m1_pre_topc @ X0 @ sk_B))),
% 0.17/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.17/0.51  thf('122', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.17/0.51      inference('sup-', [status(thm)], ['120', '121'])).
% 0.17/0.51  thf('123', plain,
% 0.17/0.51      (![X0 : $i, X1 : $i]:
% 0.17/0.51         (~ (l1_pre_topc @ X0)
% 0.17/0.51          | ~ (l1_pre_topc @ X1)
% 0.17/0.51          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.17/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.17/0.51          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.17/0.51      inference('sup-', [status(thm)], ['56', '57'])).
% 0.17/0.51  thf('124', plain,
% 0.17/0.51      (((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.17/0.51         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.17/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.17/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.17/0.51      inference('sup-', [status(thm)], ['122', '123'])).
% 0.17/0.51  thf('125', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('126', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('127', plain,
% 0.17/0.51      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.17/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.17/0.51      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.17/0.51  thf('128', plain,
% 0.17/0.51      (![X19 : $i, X20 : $i]:
% 0.17/0.51         (~ (m1_subset_1 @ X19 @ 
% 0.17/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.17/0.51          | ~ (r1_tarski @ X19 @ (u1_pre_topc @ X20))
% 0.17/0.51          | (v1_tops_2 @ X19 @ X20)
% 0.17/0.51          | ~ (l1_pre_topc @ X20))),
% 0.17/0.51      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.17/0.51  thf('129', plain,
% 0.17/0.51      ((~ (l1_pre_topc @ sk_B)
% 0.17/0.51        | (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_B)
% 0.17/0.51        | ~ (r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.17/0.51      inference('sup-', [status(thm)], ['127', '128'])).
% 0.17/0.51  thf('130', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('131', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.17/0.51      inference('simplify', [status(thm)], ['95'])).
% 0.17/0.51  thf('132', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_B)),
% 0.17/0.51      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.17/0.51  thf('133', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A)),
% 0.17/0.51      inference('demod', [status(thm)], ['116', '117', '118', '119', '132'])).
% 0.17/0.51  thf('134', plain,
% 0.17/0.51      ((r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.17/0.51      inference('demod', [status(thm)], ['111', '133'])).
% 0.17/0.51  thf('135', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.17/0.51      inference('demod', [status(thm)], ['101', '134'])).
% 0.17/0.51  thf('136', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('137', plain,
% 0.17/0.51      ((((u1_pre_topc @ sk_A)
% 0.17/0.51          != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.17/0.51        | (v2_tdlat_3 @ sk_B))),
% 0.17/0.51      inference('demod', [status(thm)], ['54', '135', '136'])).
% 0.17/0.51  thf('138', plain, (~ (v2_tdlat_3 @ sk_B)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('139', plain,
% 0.17/0.51      (((u1_pre_topc @ sk_A)
% 0.17/0.51         != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.51      inference('clc', [status(thm)], ['137', '138'])).
% 0.17/0.51  thf('140', plain,
% 0.17/0.51      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.17/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.17/0.51        | ~ (v2_tdlat_3 @ sk_A))),
% 0.17/0.51      inference('sup-', [status(thm)], ['0', '139'])).
% 0.17/0.51  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('142', plain, ((v2_tdlat_3 @ sk_A)),
% 0.17/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.51  thf('143', plain, (((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))),
% 0.17/0.51      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.17/0.51  thf('144', plain, ($false), inference('simplify', [status(thm)], ['143'])).
% 0.17/0.51  
% 0.17/0.51  % SZS output end Refutation
% 0.17/0.51  
% 0.17/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
