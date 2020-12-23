%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B0IZNBiMS7

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:07 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  207 (1448 expanded)
%              Number of leaves         :   30 ( 432 expanded)
%              Depth                    :   23
%              Number of atoms          : 1718 (22463 expanded)
%              Number of equality atoms :   40 ( 652 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(t13_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
               => ( ( ( v1_borsuk_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( ( v1_borsuk_1 @ C @ A )
                    & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v2_pre_topc @ C )
                  & ( l1_pre_topc @ C ) )
               => ( ( C
                    = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                 => ( ( ( v1_borsuk_1 @ B @ A )
                      & ( m1_pre_topc @ B @ A ) )
                  <=> ( ( v1_borsuk_1 @ C @ A )
                      & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_tmap_1])).

thf('0',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t11_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_borsuk_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( X16
       != ( u1_struct_0 @ X14 ) )
      | ~ ( v4_pre_topc @ X16 @ X15 )
      | ( v1_borsuk_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v1_borsuk_1 @ X14 @ X15 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X14 ) @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_borsuk_1 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_borsuk_1 @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('14',plain,(
    ! [X13: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('17',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('18',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_pre_topc @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('28',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('29',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','25','26','29'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X13: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('36',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_pre_topc @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v3_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) ) )
      | ( v3_pre_topc @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) ) )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,
    ( ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( l1_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61','64'])).

thf('66',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','67'])).

thf('69',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('70',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','67'])).

thf('71',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('73',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','73'])).

thf('75',plain,
    ( ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_B ) @ sk_A )
      | ( v1_borsuk_1 @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','74'])).

thf('76',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['76'])).

thf('78',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['78'])).

thf('80',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( B
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
               => ( ( m1_pre_topc @ B @ A )
                <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('81',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ( X17
       != ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ~ ( m1_pre_topc @ X17 @ X19 )
      | ( m1_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('82',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( m1_pre_topc @ X18 @ X19 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) @ X19 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87','88','89'])).

thf('91',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['79','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['94'])).

thf('96',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['93','95'])).

thf('97',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['77','96'])).

thf('98',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_B ) @ sk_A )
    | ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['75','97'])).

thf('99',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('101',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('103',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A )
    | ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['98','103'])).

thf('105',plain,
    ( ~ ( v1_borsuk_1 @ sk_B @ sk_A )
   <= ~ ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['94'])).

thf('106',plain,
    ( ~ ( v1_borsuk_1 @ sk_B @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['94'])).

thf('107',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('108',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ( X17
       != ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_pre_topc @ X17 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('110',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115','116','117'])).

thf('119',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['107','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
   <= ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['94'])).

thf('123',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('125',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
    | ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
   <= ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['125'])).

thf('127',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('128',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( X16
       != ( u1_struct_0 @ X14 ) )
      | ~ ( v1_borsuk_1 @ X14 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v4_pre_topc @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('129',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X14 ) @ X15 )
      | ~ ( v1_borsuk_1 @ X14 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v1_borsuk_1 @ sk_B @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['127','129'])).

thf('131',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('132',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( ~ ( v1_borsuk_1 @ sk_B @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf('135',plain,
    ( ( v4_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','134'])).

thf('136',plain,
    ( ( ( v4_pre_topc @ ( k2_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( v1_borsuk_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['124','135'])).

thf('137',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('138',plain,
    ( ( v4_pre_topc @ ( k2_struct_0 @ sk_B ) @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('140',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['78'])).

thf('141',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('142',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v1_borsuk_1 @ X14 @ X15 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X14 ) @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('146',plain,
    ( ( ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_borsuk_1 @ sk_C @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['78'])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_borsuk_1 @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,
    ( ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_B ) @ sk_A )
      | ( v1_borsuk_1 @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['139','150'])).

thf('152',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['138','151'])).

thf('153',plain,
    ( ~ ( v1_borsuk_1 @ sk_C @ sk_A )
   <= ~ ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['94'])).

thf('154',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['106','77','96','123','154'])).

thf('156',plain,(
    ~ ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['105','155'])).

thf('157',plain,(
    ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A ) ),
    inference(clc,[status(thm)],['104','156'])).

thf('158',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
   <= ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['125'])).

thf('159',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('160',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X14 ) @ X15 )
      | ~ ( v1_borsuk_1 @ X14 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('161',plain,
    ( ( ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v1_borsuk_1 @ sk_C @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['78'])).

thf('163',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( ~ ( v1_borsuk_1 @ sk_C @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('166',plain,
    ( ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['158','165'])).

thf('167',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('168',plain,
    ( ( v4_pre_topc @ ( k2_struct_0 @ sk_B ) @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
    | ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['125'])).

thf('170',plain,(
    v1_borsuk_1 @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['106','77','96','123','154','169'])).

thf('171',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['77','96','123'])).

thf('172',plain,(
    v4_pre_topc @ ( k2_struct_0 @ sk_B ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['168','170','171'])).

thf('173',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('174',plain,(
    v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    $false ),
    inference(demod,[status(thm)],['157','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B0IZNBiMS7
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 461 iterations in 0.203s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.66  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.47/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.66  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.47/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.47/0.66  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.66  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.66  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 0.47/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.66  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.47/0.66  thf(t13_tmap_1, conjecture,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.47/0.66           ( ![C:$i]:
% 0.47/0.66             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.47/0.66               ( ( ( C ) =
% 0.47/0.66                   ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.47/0.66                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.47/0.66                   ( ( v1_borsuk_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i]:
% 0.47/0.66        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.66          ( ![B:$i]:
% 0.47/0.66            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.47/0.66              ( ![C:$i]:
% 0.47/0.66                ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.47/0.66                  ( ( ( C ) =
% 0.47/0.66                      ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.47/0.66                    ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.47/0.66                      ( ( v1_borsuk_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t13_tmap_1])).
% 0.47/0.66  thf('0', plain,
% 0.47/0.66      (((v1_borsuk_1 @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf(t1_tsep_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_pre_topc @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_pre_topc @ B @ A ) =>
% 0.47/0.66           ( m1_subset_1 @
% 0.47/0.66             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (![X20 : $i, X21 : $i]:
% 0.47/0.66         (~ (m1_pre_topc @ X20 @ X21)
% 0.47/0.66          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.47/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.47/0.66          | ~ (l1_pre_topc @ X21))),
% 0.47/0.66      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (((~ (l1_pre_topc @ sk_A)
% 0.47/0.66         | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.66            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.47/0.66         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.66  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.47/0.66         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['3', '4'])).
% 0.47/0.66  thf(t11_tsep_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_pre_topc @ B @ A ) =>
% 0.47/0.66           ( ![C:$i]:
% 0.47/0.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.47/0.66                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.47/0.66                   ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.66         (~ (m1_pre_topc @ X14 @ X15)
% 0.47/0.66          | ((X16) != (u1_struct_0 @ X14))
% 0.47/0.66          | ~ (v4_pre_topc @ X16 @ X15)
% 0.47/0.66          | (v1_borsuk_1 @ X14 @ X15)
% 0.47/0.66          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.47/0.66          | ~ (l1_pre_topc @ X15)
% 0.47/0.66          | ~ (v2_pre_topc @ X15))),
% 0.47/0.66      inference('cnf', [status(esa)], [t11_tsep_1])).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i]:
% 0.47/0.66         (~ (v2_pre_topc @ X15)
% 0.47/0.66          | ~ (l1_pre_topc @ X15)
% 0.47/0.66          | ~ (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.47/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.47/0.66          | (v1_borsuk_1 @ X14 @ X15)
% 0.47/0.66          | ~ (v4_pre_topc @ (u1_struct_0 @ X14) @ X15)
% 0.47/0.66          | ~ (m1_pre_topc @ X14 @ X15))),
% 0.47/0.66      inference('simplify', [status(thm)], ['6'])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.47/0.66         | ~ (v4_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.47/0.66         | (v1_borsuk_1 @ sk_B @ sk_A)
% 0.47/0.66         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.66         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['5', '7'])).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      (((~ (v4_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.47/0.66         | (v1_borsuk_1 @ sk_B @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(fc10_tops_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.66       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (![X13 : $i]:
% 0.47/0.66         ((v3_pre_topc @ (k2_struct_0 @ X13) @ X13)
% 0.47/0.66          | ~ (l1_pre_topc @ X13)
% 0.47/0.66          | ~ (v2_pre_topc @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.47/0.66  thf(d3_struct_0, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (![X8 : $i]:
% 0.47/0.66         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.66  thf(dt_k2_subset_1, axiom,
% 0.47/0.66    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.47/0.66  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.47/0.66  thf('17', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.47/0.66  thf('18', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.47/0.66      inference('demod', [status(thm)], ['16', '17'])).
% 0.47/0.66  thf(t60_pre_topc, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( ( v3_pre_topc @ B @ A ) & 
% 0.47/0.66             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.47/0.66           ( ( v3_pre_topc @
% 0.47/0.66               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.47/0.66             ( m1_subset_1 @
% 0.47/0.66               B @ 
% 0.47/0.66               ( k1_zfmisc_1 @
% 0.47/0.66                 ( u1_struct_0 @
% 0.47/0.66                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      (![X11 : $i, X12 : $i]:
% 0.47/0.66         (~ (v3_pre_topc @ X12 @ X11)
% 0.47/0.66          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.47/0.66          | (m1_subset_1 @ X12 @ 
% 0.47/0.66             (k1_zfmisc_1 @ 
% 0.47/0.66              (u1_struct_0 @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))))
% 0.47/0.66          | ~ (l1_pre_topc @ X11)
% 0.47/0.66          | ~ (v2_pre_topc @ X11))),
% 0.47/0.66      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v2_pre_topc @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.47/0.66             (k1_zfmisc_1 @ 
% 0.47/0.66              (u1_struct_0 @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.47/0.66          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.66  thf('21', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.47/0.66          | ~ (l1_struct_0 @ X0)
% 0.47/0.66          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.47/0.66             (k1_zfmisc_1 @ 
% 0.47/0.66              (u1_struct_0 @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | ~ (v2_pre_topc @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['15', '20'])).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v2_pre_topc @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | ~ (v2_pre_topc @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.47/0.66             (k1_zfmisc_1 @ 
% 0.47/0.66              (u1_struct_0 @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.47/0.66          | ~ (l1_struct_0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['14', '21'])).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_struct_0 @ X0)
% 0.47/0.66          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.47/0.66             (k1_zfmisc_1 @ 
% 0.47/0.66              (u1_struct_0 @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | ~ (v2_pre_topc @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['22'])).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.47/0.66        | ~ (v2_pre_topc @ sk_B)
% 0.47/0.66        | ~ (l1_pre_topc @ sk_B)
% 0.47/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.66      inference('sup+', [status(thm)], ['13', '23'])).
% 0.47/0.66  thf('25', plain, ((v2_pre_topc @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(dt_l1_pre_topc, axiom,
% 0.47/0.66    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.47/0.66  thf('28', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.66  thf('29', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.66      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.47/0.66      inference('demod', [status(thm)], ['24', '25', '26', '29'])).
% 0.47/0.66  thf(t3_subset, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i]:
% 0.47/0.66         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.66  thf('32', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.47/0.66      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.66  thf(d10_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      (![X0 : $i, X2 : $i]:
% 0.47/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.47/0.66        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      (![X13 : $i]:
% 0.47/0.66         ((v3_pre_topc @ (k2_struct_0 @ X13) @ X13)
% 0.47/0.66          | ~ (l1_pre_topc @ X13)
% 0.47/0.66          | ~ (v2_pre_topc @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (![X8 : $i]:
% 0.47/0.66         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.66  thf('37', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.47/0.66      inference('demod', [status(thm)], ['16', '17'])).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      (![X11 : $i, X12 : $i]:
% 0.47/0.66         (~ (v3_pre_topc @ X12 @ X11)
% 0.47/0.66          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.47/0.66          | (v3_pre_topc @ X12 @ 
% 0.47/0.66             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.47/0.66          | ~ (l1_pre_topc @ X11)
% 0.47/0.66          | ~ (v2_pre_topc @ X11))),
% 0.47/0.66      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v2_pre_topc @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.47/0.66             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.66          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.47/0.66          | ~ (l1_struct_0 @ X0)
% 0.47/0.66          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.47/0.66             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | ~ (v2_pre_topc @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['36', '39'])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v2_pre_topc @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | ~ (v2_pre_topc @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.47/0.66             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.66          | ~ (l1_struct_0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['35', '40'])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_struct_0 @ X0)
% 0.47/0.66          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.47/0.66             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | ~ (v2_pre_topc @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['41'])).
% 0.47/0.66  thf('43', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_struct_0 @ X0)
% 0.47/0.66          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.47/0.66             (k1_zfmisc_1 @ 
% 0.47/0.66              (u1_struct_0 @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | ~ (v2_pre_topc @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['22'])).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      (![X10 : $i, X11 : $i]:
% 0.47/0.66         (~ (v3_pre_topc @ X10 @ 
% 0.47/0.66             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.47/0.66          | ~ (m1_subset_1 @ X10 @ 
% 0.47/0.66               (k1_zfmisc_1 @ 
% 0.47/0.66                (u1_struct_0 @ 
% 0.47/0.66                 (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))))
% 0.47/0.66          | (v3_pre_topc @ X10 @ X11)
% 0.47/0.66          | ~ (l1_pre_topc @ X11)
% 0.47/0.66          | ~ (v2_pre_topc @ X11))),
% 0.47/0.66      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v2_pre_topc @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | ~ (l1_struct_0 @ X0)
% 0.47/0.66          | ~ (v2_pre_topc @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.66          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.66  thf('46', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.47/0.66             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.66          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.66          | ~ (l1_struct_0 @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | ~ (v2_pre_topc @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['45'])).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v2_pre_topc @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | ~ (l1_struct_0 @ X0)
% 0.47/0.66          | ~ (v2_pre_topc @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | ~ (l1_struct_0 @ X0)
% 0.47/0.66          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['42', '46'])).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.66          | ~ (l1_struct_0 @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | ~ (v2_pre_topc @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['47'])).
% 0.47/0.66  thf('49', plain,
% 0.47/0.66      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('50', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.47/0.66      inference('demod', [status(thm)], ['16', '17'])).
% 0.47/0.66  thf('51', plain,
% 0.47/0.66      (![X10 : $i, X11 : $i]:
% 0.47/0.66         (~ (v3_pre_topc @ X10 @ 
% 0.47/0.66             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.47/0.66          | ~ (m1_subset_1 @ X10 @ 
% 0.47/0.66               (k1_zfmisc_1 @ 
% 0.47/0.66                (u1_struct_0 @ 
% 0.47/0.66                 (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))))
% 0.47/0.66          | (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.47/0.66          | ~ (l1_pre_topc @ X11)
% 0.47/0.66          | ~ (v2_pre_topc @ X11))),
% 0.47/0.66      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.47/0.66  thf('52', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v2_pre_topc @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | (m1_subset_1 @ 
% 0.47/0.66             (u1_struct_0 @ 
% 0.47/0.66              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.47/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.47/0.66          | ~ (v3_pre_topc @ 
% 0.47/0.66               (u1_struct_0 @ 
% 0.47/0.66                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.66  thf('53', plain,
% 0.47/0.66      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ 
% 0.47/0.66           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.47/0.66        | (m1_subset_1 @ 
% 0.47/0.66           (u1_struct_0 @ 
% 0.47/0.66            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.47/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.47/0.66        | ~ (l1_pre_topc @ sk_B)
% 0.47/0.66        | ~ (v2_pre_topc @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['49', '52'])).
% 0.47/0.66  thf('54', plain,
% 0.47/0.66      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('55', plain,
% 0.47/0.66      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('56', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('57', plain, ((v2_pre_topc @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('58', plain,
% 0.47/0.66      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 0.47/0.66        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.47/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.47/0.66      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.47/0.66  thf('59', plain,
% 0.47/0.66      ((~ (v2_pre_topc @ sk_C)
% 0.47/0.66        | ~ (l1_pre_topc @ sk_C)
% 0.47/0.66        | ~ (l1_struct_0 @ sk_C)
% 0.47/0.66        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.47/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['48', '58'])).
% 0.47/0.66  thf('60', plain, ((v2_pre_topc @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('61', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('62', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('63', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.66  thf('64', plain, ((l1_struct_0 @ sk_C)),
% 0.47/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.66  thf('65', plain,
% 0.47/0.66      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.47/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['59', '60', '61', '64'])).
% 0.47/0.66  thf('66', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i]:
% 0.47/0.66         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.66  thf('67', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['65', '66'])).
% 0.47/0.66  thf('68', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['34', '67'])).
% 0.47/0.66  thf('69', plain,
% 0.47/0.66      (![X8 : $i]:
% 0.47/0.66         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.66  thf('70', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['34', '67'])).
% 0.47/0.66  thf('71', plain,
% 0.47/0.66      ((((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_B)) | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.66      inference('sup+', [status(thm)], ['69', '70'])).
% 0.47/0.66  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.66      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.66  thf('73', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['71', '72'])).
% 0.47/0.66  thf('74', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['68', '73'])).
% 0.47/0.66  thf('75', plain,
% 0.47/0.66      (((~ (v4_pre_topc @ (k2_struct_0 @ sk_B) @ sk_A)
% 0.47/0.66         | (v1_borsuk_1 @ sk_B @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['12', '74'])).
% 0.47/0.66  thf('76', plain,
% 0.47/0.66      (((m1_pre_topc @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('77', plain,
% 0.47/0.66      (((m1_pre_topc @ sk_C @ sk_A)) | ((m1_pre_topc @ sk_B @ sk_A))),
% 0.47/0.66      inference('split', [status(esa)], ['76'])).
% 0.47/0.66  thf('78', plain,
% 0.47/0.66      (((m1_pre_topc @ sk_C @ sk_A) | (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('79', plain,
% 0.47/0.66      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['78'])).
% 0.47/0.66  thf('80', plain,
% 0.47/0.66      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(t12_tmap_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_pre_topc @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.47/0.66           ( ![C:$i]:
% 0.47/0.66             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.47/0.66               ( ( ( B ) =
% 0.47/0.66                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.47/0.66                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf('81', plain,
% 0.47/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.66         (~ (v2_pre_topc @ X17)
% 0.47/0.66          | ~ (l1_pre_topc @ X17)
% 0.47/0.66          | ((X17) != (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 0.47/0.66          | ~ (m1_pre_topc @ X17 @ X19)
% 0.47/0.66          | (m1_pre_topc @ X18 @ X19)
% 0.47/0.66          | ~ (l1_pre_topc @ X18)
% 0.47/0.66          | ~ (v2_pre_topc @ X18)
% 0.47/0.66          | ~ (l1_pre_topc @ X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.47/0.66  thf('82', plain,
% 0.47/0.66      (![X18 : $i, X19 : $i]:
% 0.47/0.66         (~ (l1_pre_topc @ X19)
% 0.47/0.66          | ~ (v2_pre_topc @ X18)
% 0.47/0.66          | ~ (l1_pre_topc @ X18)
% 0.47/0.66          | (m1_pre_topc @ X18 @ X19)
% 0.47/0.66          | ~ (m1_pre_topc @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)) @ X19)
% 0.47/0.66          | ~ (l1_pre_topc @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 0.47/0.66          | ~ (v2_pre_topc @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['81'])).
% 0.47/0.66  thf('83', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_pre_topc @ sk_C)
% 0.47/0.66          | ~ (v2_pre_topc @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.47/0.66          | ~ (m1_pre_topc @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.47/0.66          | (m1_pre_topc @ sk_B @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ sk_B)
% 0.47/0.66          | ~ (v2_pre_topc @ sk_B)
% 0.47/0.66          | ~ (l1_pre_topc @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['80', '82'])).
% 0.47/0.66  thf('84', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('85', plain,
% 0.47/0.66      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('86', plain, ((v2_pre_topc @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('87', plain,
% 0.47/0.66      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('88', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('89', plain, ((v2_pre_topc @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('90', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.66          | (m1_pre_topc @ sk_B @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0))),
% 0.47/0.66      inference('demod', [status(thm)],
% 0.47/0.66                ['83', '84', '85', '86', '87', '88', '89'])).
% 0.47/0.66  thf('91', plain,
% 0.47/0.66      (((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A)))
% 0.47/0.66         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['79', '90'])).
% 0.47/0.66  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('93', plain,
% 0.47/0.66      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['91', '92'])).
% 0.47/0.66  thf('94', plain,
% 0.47/0.66      ((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.47/0.66        | ~ (v1_borsuk_1 @ sk_C @ sk_A)
% 0.47/0.66        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.47/0.66        | ~ (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('95', plain,
% 0.47/0.66      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['94'])).
% 0.47/0.66  thf('96', plain,
% 0.47/0.66      (((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['93', '95'])).
% 0.47/0.66  thf('97', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['77', '96'])).
% 0.47/0.66  thf('98', plain,
% 0.47/0.66      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_B) @ sk_A)
% 0.47/0.66        | (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['75', '97'])).
% 0.47/0.66  thf('99', plain,
% 0.47/0.66      (![X8 : $i]:
% 0.47/0.66         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.66  thf('100', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['71', '72'])).
% 0.47/0.66  thf('101', plain,
% 0.47/0.66      ((((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_B)) | ~ (l1_struct_0 @ sk_C))),
% 0.47/0.66      inference('sup+', [status(thm)], ['99', '100'])).
% 0.47/0.66  thf('102', plain, ((l1_struct_0 @ sk_C)),
% 0.47/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.66  thf('103', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['101', '102'])).
% 0.47/0.66  thf('104', plain,
% 0.47/0.66      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)
% 0.47/0.66        | (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['98', '103'])).
% 0.47/0.66  thf('105', plain,
% 0.47/0.66      ((~ (v1_borsuk_1 @ sk_B @ sk_A)) <= (~ ((v1_borsuk_1 @ sk_B @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['94'])).
% 0.47/0.66  thf('106', plain,
% 0.47/0.66      (~ ((v1_borsuk_1 @ sk_B @ sk_A)) | ~ ((v1_borsuk_1 @ sk_C @ sk_A)) | 
% 0.47/0.66       ~ ((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.47/0.66      inference('split', [status(esa)], ['94'])).
% 0.47/0.66  thf('107', plain,
% 0.47/0.66      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('108', plain,
% 0.47/0.66      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('109', plain,
% 0.47/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.66         (~ (v2_pre_topc @ X17)
% 0.47/0.66          | ~ (l1_pre_topc @ X17)
% 0.47/0.66          | ((X17) != (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 0.47/0.66          | ~ (m1_pre_topc @ X18 @ X19)
% 0.47/0.66          | (m1_pre_topc @ X17 @ X19)
% 0.47/0.66          | ~ (l1_pre_topc @ X18)
% 0.47/0.66          | ~ (v2_pre_topc @ X18)
% 0.47/0.66          | ~ (l1_pre_topc @ X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.47/0.66  thf('110', plain,
% 0.47/0.66      (![X18 : $i, X19 : $i]:
% 0.47/0.66         (~ (l1_pre_topc @ X19)
% 0.47/0.66          | ~ (v2_pre_topc @ X18)
% 0.47/0.66          | ~ (l1_pre_topc @ X18)
% 0.47/0.66          | (m1_pre_topc @ 
% 0.47/0.66             (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)) @ X19)
% 0.47/0.66          | ~ (m1_pre_topc @ X18 @ X19)
% 0.47/0.66          | ~ (l1_pre_topc @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 0.47/0.66          | ~ (v2_pre_topc @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['109'])).
% 0.47/0.66  thf('111', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_pre_topc @ sk_C)
% 0.47/0.66          | ~ (v2_pre_topc @ 
% 0.47/0.66               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.47/0.66          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.47/0.66          | (m1_pre_topc @ 
% 0.47/0.66             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ sk_B)
% 0.47/0.66          | ~ (v2_pre_topc @ sk_B)
% 0.47/0.66          | ~ (l1_pre_topc @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['108', '110'])).
% 0.47/0.66  thf('112', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('113', plain,
% 0.47/0.66      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('114', plain, ((v2_pre_topc @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('115', plain,
% 0.47/0.66      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('116', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('117', plain, ((v2_pre_topc @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('118', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_pre_topc @ sk_B @ X0)
% 0.47/0.66          | (m1_pre_topc @ sk_C @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0))),
% 0.47/0.66      inference('demod', [status(thm)],
% 0.47/0.66                ['111', '112', '113', '114', '115', '116', '117'])).
% 0.47/0.66  thf('119', plain,
% 0.47/0.66      (((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_C @ sk_A)))
% 0.47/0.66         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['107', '118'])).
% 0.47/0.66  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('121', plain,
% 0.47/0.66      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['119', '120'])).
% 0.47/0.66  thf('122', plain,
% 0.47/0.66      ((~ (m1_pre_topc @ sk_C @ sk_A)) <= (~ ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['94'])).
% 0.47/0.66  thf('123', plain,
% 0.47/0.66      (((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['121', '122'])).
% 0.47/0.66  thf('124', plain,
% 0.47/0.66      (![X8 : $i]:
% 0.47/0.66         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.66  thf('125', plain,
% 0.47/0.66      (((v1_borsuk_1 @ sk_C @ sk_A) | (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('126', plain,
% 0.47/0.66      (((v1_borsuk_1 @ sk_B @ sk_A)) <= (((v1_borsuk_1 @ sk_B @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['125'])).
% 0.47/0.66  thf('127', plain,
% 0.47/0.66      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.47/0.66         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['3', '4'])).
% 0.47/0.66  thf('128', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.66         (~ (m1_pre_topc @ X14 @ X15)
% 0.47/0.66          | ((X16) != (u1_struct_0 @ X14))
% 0.47/0.66          | ~ (v1_borsuk_1 @ X14 @ X15)
% 0.47/0.66          | ~ (m1_pre_topc @ X14 @ X15)
% 0.47/0.66          | (v4_pre_topc @ X16 @ X15)
% 0.47/0.66          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.47/0.66          | ~ (l1_pre_topc @ X15)
% 0.47/0.66          | ~ (v2_pre_topc @ X15))),
% 0.47/0.66      inference('cnf', [status(esa)], [t11_tsep_1])).
% 0.47/0.66  thf('129', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i]:
% 0.47/0.66         (~ (v2_pre_topc @ X15)
% 0.47/0.66          | ~ (l1_pre_topc @ X15)
% 0.47/0.66          | ~ (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.47/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.47/0.66          | (v4_pre_topc @ (u1_struct_0 @ X14) @ X15)
% 0.47/0.66          | ~ (v1_borsuk_1 @ X14 @ X15)
% 0.47/0.66          | ~ (m1_pre_topc @ X14 @ X15))),
% 0.47/0.66      inference('simplify', [status(thm)], ['128'])).
% 0.47/0.66  thf('130', plain,
% 0.47/0.66      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.47/0.66         | ~ (v1_borsuk_1 @ sk_B @ sk_A)
% 0.47/0.66         | (v4_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.47/0.66         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.66         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['127', '129'])).
% 0.47/0.66  thf('131', plain,
% 0.47/0.66      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('132', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('133', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('134', plain,
% 0.47/0.66      (((~ (v1_borsuk_1 @ sk_B @ sk_A)
% 0.47/0.66         | (v4_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)))
% 0.47/0.66         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 0.47/0.66  thf('135', plain,
% 0.47/0.66      (((v4_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.47/0.66         <= (((v1_borsuk_1 @ sk_B @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['126', '134'])).
% 0.47/0.66  thf('136', plain,
% 0.47/0.66      ((((v4_pre_topc @ (k2_struct_0 @ sk_B) @ sk_A) | ~ (l1_struct_0 @ sk_B)))
% 0.47/0.66         <= (((v1_borsuk_1 @ sk_B @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['124', '135'])).
% 0.47/0.66  thf('137', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.66      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.66  thf('138', plain,
% 0.47/0.66      (((v4_pre_topc @ (k2_struct_0 @ sk_B) @ sk_A))
% 0.47/0.66         <= (((v1_borsuk_1 @ sk_B @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['136', '137'])).
% 0.47/0.66  thf('139', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['71', '72'])).
% 0.47/0.66  thf('140', plain,
% 0.47/0.66      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['78'])).
% 0.47/0.66  thf('141', plain,
% 0.47/0.66      (![X20 : $i, X21 : $i]:
% 0.47/0.66         (~ (m1_pre_topc @ X20 @ X21)
% 0.47/0.66          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.47/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.47/0.66          | ~ (l1_pre_topc @ X21))),
% 0.47/0.66      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.47/0.66  thf('142', plain,
% 0.47/0.66      (((~ (l1_pre_topc @ sk_A)
% 0.47/0.66         | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.47/0.66            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.47/0.66         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['140', '141'])).
% 0.47/0.66  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('144', plain,
% 0.47/0.66      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.47/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.47/0.66         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['142', '143'])).
% 0.47/0.66  thf('145', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i]:
% 0.47/0.66         (~ (v2_pre_topc @ X15)
% 0.47/0.66          | ~ (l1_pre_topc @ X15)
% 0.47/0.66          | ~ (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.47/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.47/0.66          | (v1_borsuk_1 @ X14 @ X15)
% 0.47/0.66          | ~ (v4_pre_topc @ (u1_struct_0 @ X14) @ X15)
% 0.47/0.66          | ~ (m1_pre_topc @ X14 @ X15))),
% 0.47/0.66      inference('simplify', [status(thm)], ['6'])).
% 0.47/0.66  thf('146', plain,
% 0.47/0.66      (((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.47/0.66         | ~ (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.47/0.66         | (v1_borsuk_1 @ sk_C @ sk_A)
% 0.47/0.66         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.66         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['144', '145'])).
% 0.47/0.66  thf('147', plain,
% 0.47/0.66      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['78'])).
% 0.47/0.66  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('149', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('150', plain,
% 0.47/0.66      (((~ (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.47/0.66         | (v1_borsuk_1 @ sk_C @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 0.47/0.66  thf('151', plain,
% 0.47/0.66      (((~ (v4_pre_topc @ (k2_struct_0 @ sk_B) @ sk_A)
% 0.47/0.66         | (v1_borsuk_1 @ sk_C @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['139', '150'])).
% 0.47/0.66  thf('152', plain,
% 0.47/0.66      (((v1_borsuk_1 @ sk_C @ sk_A))
% 0.47/0.66         <= (((v1_borsuk_1 @ sk_B @ sk_A)) & 
% 0.47/0.66             ((m1_pre_topc @ sk_B @ sk_A)) & 
% 0.47/0.66             ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['138', '151'])).
% 0.47/0.66  thf('153', plain,
% 0.47/0.66      ((~ (v1_borsuk_1 @ sk_C @ sk_A)) <= (~ ((v1_borsuk_1 @ sk_C @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['94'])).
% 0.47/0.66  thf('154', plain,
% 0.47/0.66      (((v1_borsuk_1 @ sk_C @ sk_A)) | ~ ((v1_borsuk_1 @ sk_B @ sk_A)) | 
% 0.47/0.66       ~ ((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['152', '153'])).
% 0.47/0.66  thf('155', plain, (~ ((v1_borsuk_1 @ sk_B @ sk_A))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)],
% 0.47/0.66                ['106', '77', '96', '123', '154'])).
% 0.47/0.66  thf('156', plain, (~ (v1_borsuk_1 @ sk_B @ sk_A)),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['105', '155'])).
% 0.47/0.66  thf('157', plain, (~ (v4_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)),
% 0.47/0.66      inference('clc', [status(thm)], ['104', '156'])).
% 0.47/0.66  thf('158', plain,
% 0.47/0.66      (((v1_borsuk_1 @ sk_C @ sk_A)) <= (((v1_borsuk_1 @ sk_C @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['125'])).
% 0.47/0.66  thf('159', plain,
% 0.47/0.66      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.47/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.47/0.66         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['142', '143'])).
% 0.47/0.66  thf('160', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i]:
% 0.47/0.66         (~ (v2_pre_topc @ X15)
% 0.47/0.66          | ~ (l1_pre_topc @ X15)
% 0.47/0.66          | ~ (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.47/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.47/0.66          | (v4_pre_topc @ (u1_struct_0 @ X14) @ X15)
% 0.47/0.66          | ~ (v1_borsuk_1 @ X14 @ X15)
% 0.47/0.66          | ~ (m1_pre_topc @ X14 @ X15))),
% 0.47/0.66      inference('simplify', [status(thm)], ['128'])).
% 0.47/0.66  thf('161', plain,
% 0.47/0.66      (((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.47/0.66         | ~ (v1_borsuk_1 @ sk_C @ sk_A)
% 0.47/0.66         | (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.47/0.66         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.66         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['159', '160'])).
% 0.47/0.66  thf('162', plain,
% 0.47/0.66      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['78'])).
% 0.47/0.66  thf('163', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('164', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('165', plain,
% 0.47/0.66      (((~ (v1_borsuk_1 @ sk_C @ sk_A)
% 0.47/0.66         | (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)))
% 0.47/0.66         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 0.47/0.66  thf('166', plain,
% 0.47/0.66      (((v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A))
% 0.47/0.66         <= (((v1_borsuk_1 @ sk_C @ sk_A)) & ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['158', '165'])).
% 0.47/0.66  thf('167', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['71', '72'])).
% 0.47/0.66  thf('168', plain,
% 0.47/0.66      (((v4_pre_topc @ (k2_struct_0 @ sk_B) @ sk_A))
% 0.47/0.66         <= (((v1_borsuk_1 @ sk_C @ sk_A)) & ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['166', '167'])).
% 0.47/0.66  thf('169', plain,
% 0.47/0.66      (((v1_borsuk_1 @ sk_C @ sk_A)) | ((v1_borsuk_1 @ sk_B @ sk_A))),
% 0.47/0.66      inference('split', [status(esa)], ['125'])).
% 0.47/0.66  thf('170', plain, (((v1_borsuk_1 @ sk_C @ sk_A))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)],
% 0.47/0.66                ['106', '77', '96', '123', '154', '169'])).
% 0.47/0.66  thf('171', plain, (((m1_pre_topc @ sk_C @ sk_A))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['77', '96', '123'])).
% 0.47/0.66  thf('172', plain, ((v4_pre_topc @ (k2_struct_0 @ sk_B) @ sk_A)),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['168', '170', '171'])).
% 0.47/0.66  thf('173', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['101', '102'])).
% 0.47/0.66  thf('174', plain, ((v4_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)),
% 0.47/0.66      inference('demod', [status(thm)], ['172', '173'])).
% 0.47/0.66  thf('175', plain, ($false), inference('demod', [status(thm)], ['157', '174'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
