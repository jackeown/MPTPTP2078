%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jSxm86eWuU

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:08 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  207 (10317 expanded)
%              Number of leaves         :   31 (3154 expanded)
%              Depth                    :   27
%              Number of atoms          : 1641 (145992 expanded)
%              Number of equality atoms :   52 (4980 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t61_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v4_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v4_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v4_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) ) ) )
      | ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('21',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('22',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X10: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('34',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['41','42','43','46'])).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['31','49'])).

thf('51',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['31','49'])).

thf('53',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('55',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('59',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('61',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','62'])).

thf('64',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('65',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( X18
       != ( u1_struct_0 @ X16 ) )
      | ~ ( v4_pre_topc @ X18 @ X17 )
      | ( v1_borsuk_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_borsuk_1 @ X16 @ X17 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X1 )
      | ( v1_borsuk_1 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_borsuk_1 @ sk_C @ sk_A )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('72',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('73',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('75',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('76',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('81',plain,
    ( ( ( v1_borsuk_1 @ sk_C @ sk_A )
      | ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70','73','79','80'])).

thf('82',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['82'])).

thf('84',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['56','61'])).

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

thf('87',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( X19
       != ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) )
      | ~ ( m1_pre_topc @ X19 @ X21 )
      | ( m1_pre_topc @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('88',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) @ X21 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( sk_C
      = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('94',plain,
    ( sk_C
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('96',plain,
    ( sk_C
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('99',plain,
    ( sk_C
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('100',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('102',plain,
    ( sk_C
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('103',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['89','96','97','98','99','100','101','102','103','104'])).

thf('106',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['85','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['109'])).

thf('111',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['83','111'])).

thf('113',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['81','112'])).

thf('114',plain,
    ( ~ ( v1_borsuk_1 @ sk_C @ sk_A )
   <= ~ ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['109'])).

thf('115',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('116',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
   <= ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['109'])).

thf('117',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( v1_borsuk_1 @ sk_C @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['109'])).

thf('119',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
    | ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
   <= ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['119'])).

thf('121',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','62'])).

thf('122',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( X18
       != ( u1_struct_0 @ X16 ) )
      | ~ ( v1_borsuk_1 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v4_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('124',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( v1_borsuk_1 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_borsuk_1 @ X0 @ X1 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['122','124'])).

thf('126',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ~ ( v1_borsuk_1 @ sk_C @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['121','125'])).

thf('127',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('130',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('131',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('132',plain,
    ( ( ( v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A )
      | ~ ( v1_borsuk_1 @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['126','127','128','129','130','131'])).

thf('133',plain,
    ( ( v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','132'])).

thf('134',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','62'])).

thf('135',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X1 )
      | ( v1_borsuk_1 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_borsuk_1 @ sk_B @ X0 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_borsuk_1 @ sk_B @ X0 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_borsuk_1 @ sk_B @ X0 )
      | ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A )
      | ( v1_borsuk_1 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['134','141'])).

thf('143',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A )
      | ( v1_borsuk_1 @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['142','143','144','145'])).

thf('147',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','146'])).

thf('148',plain,
    ( ~ ( v1_borsuk_1 @ sk_B @ sk_A )
   <= ~ ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['109'])).

thf('149',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['117','118','83','111','149'])).

thf('151',plain,(
    ~ ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['114','150'])).

thf('152',plain,(
    ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A ) ),
    inference(clc,[status(thm)],['113','151'])).

thf('153',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','62'])).

thf('154',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['83','111'])).

thf('155',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_borsuk_1 @ X0 @ X1 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['122','124'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( v1_borsuk_1 @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( v1_borsuk_1 @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ X0 )
      | ~ ( v1_borsuk_1 @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['155','162'])).

thf('164',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('165',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['83','111'])).

thf('166',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
   <= ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['119'])).

thf('168',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
    | ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['119'])).

thf('169',plain,(
    v1_borsuk_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['117','118','83','111','149','168'])).

thf('170',plain,(
    v1_borsuk_1 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['167','169'])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v4_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['163','166','170','171','172'])).

thf('174',plain,(
    $false ),
    inference(demod,[status(thm)],['152','173'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jSxm86eWuU
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:47:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.61/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.82  % Solved by: fo/fo7.sh
% 0.61/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.82  % done 986 iterations in 0.353s
% 0.61/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.82  % SZS output start Refutation
% 0.61/0.82  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.61/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.82  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.61/0.82  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.61/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.82  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.61/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.82  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.61/0.82  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.61/0.82  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.61/0.82  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 0.61/0.82  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.61/0.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.61/0.82  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.61/0.82  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.61/0.82  thf(t13_tmap_1, conjecture,
% 0.61/0.82    (![A:$i]:
% 0.61/0.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.82       ( ![B:$i]:
% 0.61/0.82         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.61/0.82           ( ![C:$i]:
% 0.61/0.82             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.61/0.82               ( ( ( C ) =
% 0.61/0.82                   ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.61/0.82                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.61/0.82                   ( ( v1_borsuk_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ))).
% 0.61/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.82    (~( ![A:$i]:
% 0.61/0.82        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.82          ( ![B:$i]:
% 0.61/0.82            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.61/0.82              ( ![C:$i]:
% 0.61/0.82                ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.61/0.82                  ( ( ( C ) =
% 0.61/0.82                      ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.61/0.82                    ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.61/0.82                      ( ( v1_borsuk_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) )),
% 0.61/0.82    inference('cnf.neg', [status(esa)], [t13_tmap_1])).
% 0.61/0.82  thf('0', plain,
% 0.61/0.82      (((v1_borsuk_1 @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('1', plain,
% 0.61/0.82      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('split', [status(esa)], ['0'])).
% 0.61/0.82  thf(t1_tsep_1, axiom,
% 0.61/0.82    (![A:$i]:
% 0.61/0.82     ( ( l1_pre_topc @ A ) =>
% 0.61/0.82       ( ![B:$i]:
% 0.61/0.82         ( ( m1_pre_topc @ B @ A ) =>
% 0.61/0.82           ( m1_subset_1 @
% 0.61/0.82             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.61/0.82  thf('2', plain,
% 0.61/0.82      (![X22 : $i, X23 : $i]:
% 0.61/0.82         (~ (m1_pre_topc @ X22 @ X23)
% 0.61/0.82          | (m1_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.61/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.61/0.82          | ~ (l1_pre_topc @ X23))),
% 0.61/0.82      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.61/0.82  thf('3', plain,
% 0.61/0.82      (((~ (l1_pre_topc @ sk_A)
% 0.61/0.82         | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.82            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.61/0.82         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.82  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(fc4_pre_topc, axiom,
% 0.61/0.82    (![A:$i]:
% 0.61/0.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.82       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.61/0.82  thf('5', plain,
% 0.61/0.82      (![X10 : $i]:
% 0.61/0.82         ((v4_pre_topc @ (k2_struct_0 @ X10) @ X10)
% 0.61/0.82          | ~ (l1_pre_topc @ X10)
% 0.61/0.82          | ~ (v2_pre_topc @ X10))),
% 0.61/0.82      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.61/0.82  thf(d3_struct_0, axiom,
% 0.61/0.82    (![A:$i]:
% 0.61/0.82     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.61/0.82  thf('6', plain,
% 0.61/0.82      (![X8 : $i]:
% 0.61/0.82         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.61/0.82  thf('7', plain,
% 0.61/0.82      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(dt_k2_subset_1, axiom,
% 0.61/0.82    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.61/0.82  thf('8', plain,
% 0.61/0.82      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.61/0.82      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.61/0.82  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.61/0.82  thf('9', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.61/0.82      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.61/0.82  thf('10', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.61/0.82      inference('demod', [status(thm)], ['8', '9'])).
% 0.61/0.82  thf(t61_pre_topc, axiom,
% 0.61/0.82    (![A:$i]:
% 0.61/0.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.82       ( ![B:$i]:
% 0.61/0.82         ( ( ( v4_pre_topc @ B @ A ) & 
% 0.61/0.82             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.61/0.82           ( ( v4_pre_topc @
% 0.61/0.82               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.61/0.82             ( m1_subset_1 @
% 0.61/0.82               B @ 
% 0.61/0.82               ( k1_zfmisc_1 @
% 0.61/0.82                 ( u1_struct_0 @
% 0.61/0.82                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.61/0.82  thf('11', plain,
% 0.61/0.82      (![X11 : $i, X12 : $i]:
% 0.61/0.82         (~ (v4_pre_topc @ X11 @ 
% 0.61/0.82             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.61/0.82          | ~ (m1_subset_1 @ X11 @ 
% 0.61/0.82               (k1_zfmisc_1 @ 
% 0.61/0.82                (u1_struct_0 @ 
% 0.61/0.82                 (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))))
% 0.61/0.82          | (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.61/0.82          | ~ (l1_pre_topc @ X12)
% 0.61/0.82          | ~ (v2_pre_topc @ X12))),
% 0.61/0.82      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.61/0.82  thf('12', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (v2_pre_topc @ X0)
% 0.61/0.82          | ~ (l1_pre_topc @ X0)
% 0.61/0.82          | (m1_subset_1 @ 
% 0.61/0.82             (u1_struct_0 @ 
% 0.61/0.82              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.61/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.61/0.82          | ~ (v4_pre_topc @ 
% 0.61/0.82               (u1_struct_0 @ 
% 0.61/0.82                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.61/0.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.61/0.82      inference('sup-', [status(thm)], ['10', '11'])).
% 0.61/0.82  thf('13', plain,
% 0.61/0.82      ((~ (v4_pre_topc @ (u1_struct_0 @ sk_C) @ 
% 0.61/0.82           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.61/0.82        | (m1_subset_1 @ 
% 0.61/0.82           (u1_struct_0 @ 
% 0.61/0.82            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.61/0.82           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.61/0.82        | ~ (l1_pre_topc @ sk_B)
% 0.61/0.82        | ~ (v2_pre_topc @ sk_B))),
% 0.61/0.82      inference('sup-', [status(thm)], ['7', '12'])).
% 0.61/0.82  thf('14', plain,
% 0.61/0.82      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('15', plain,
% 0.61/0.82      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('16', plain, ((l1_pre_topc @ sk_B)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('17', plain, ((v2_pre_topc @ sk_B)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('18', plain,
% 0.61/0.82      ((~ (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 0.61/0.82        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.61/0.82           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.61/0.82      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.61/0.82  thf('19', plain,
% 0.61/0.82      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_C) @ sk_C)
% 0.61/0.82        | ~ (l1_struct_0 @ sk_C)
% 0.61/0.82        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.61/0.82           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.61/0.82      inference('sup-', [status(thm)], ['6', '18'])).
% 0.61/0.82  thf('20', plain, ((l1_pre_topc @ sk_C)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(dt_l1_pre_topc, axiom,
% 0.61/0.82    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.61/0.82  thf('21', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.61/0.82      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.61/0.82  thf('22', plain, ((l1_struct_0 @ sk_C)),
% 0.61/0.82      inference('sup-', [status(thm)], ['20', '21'])).
% 0.61/0.82  thf('23', plain,
% 0.61/0.82      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_C) @ sk_C)
% 0.61/0.82        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.61/0.82           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.61/0.82      inference('demod', [status(thm)], ['19', '22'])).
% 0.61/0.82  thf('24', plain,
% 0.61/0.82      ((~ (v2_pre_topc @ sk_C)
% 0.61/0.82        | ~ (l1_pre_topc @ sk_C)
% 0.61/0.82        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.61/0.82           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.61/0.82      inference('sup-', [status(thm)], ['5', '23'])).
% 0.61/0.82  thf('25', plain, ((v2_pre_topc @ sk_C)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('26', plain, ((l1_pre_topc @ sk_C)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('27', plain,
% 0.61/0.82      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.61/0.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.61/0.82      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.61/0.82  thf(t3_subset, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.61/0.82  thf('28', plain,
% 0.61/0.82      (![X5 : $i, X6 : $i]:
% 0.61/0.82         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.61/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.82  thf('29', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.61/0.82      inference('sup-', [status(thm)], ['27', '28'])).
% 0.61/0.82  thf(d10_xboole_0, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.82  thf('30', plain,
% 0.61/0.82      (![X0 : $i, X2 : $i]:
% 0.61/0.82         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.61/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.82  thf('31', plain,
% 0.61/0.82      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.61/0.82        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['29', '30'])).
% 0.61/0.82  thf('32', plain,
% 0.61/0.82      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('33', plain,
% 0.61/0.82      (![X10 : $i]:
% 0.61/0.82         ((v4_pre_topc @ (k2_struct_0 @ X10) @ X10)
% 0.61/0.82          | ~ (l1_pre_topc @ X10)
% 0.61/0.82          | ~ (v2_pre_topc @ X10))),
% 0.61/0.82      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.61/0.82  thf('34', plain,
% 0.61/0.82      (![X8 : $i]:
% 0.61/0.82         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.61/0.82  thf('35', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.61/0.82      inference('demod', [status(thm)], ['8', '9'])).
% 0.61/0.82  thf('36', plain,
% 0.61/0.82      (![X12 : $i, X13 : $i]:
% 0.61/0.82         (~ (v4_pre_topc @ X13 @ X12)
% 0.61/0.82          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.61/0.82          | (m1_subset_1 @ X13 @ 
% 0.61/0.82             (k1_zfmisc_1 @ 
% 0.61/0.82              (u1_struct_0 @ 
% 0.61/0.82               (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))))
% 0.61/0.82          | ~ (l1_pre_topc @ X12)
% 0.61/0.82          | ~ (v2_pre_topc @ X12))),
% 0.61/0.82      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.61/0.82  thf('37', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (v2_pre_topc @ X0)
% 0.61/0.82          | ~ (l1_pre_topc @ X0)
% 0.61/0.82          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.61/0.82             (k1_zfmisc_1 @ 
% 0.61/0.82              (u1_struct_0 @ 
% 0.61/0.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.61/0.82          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['35', '36'])).
% 0.61/0.82  thf('38', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.61/0.82          | ~ (l1_struct_0 @ X0)
% 0.61/0.82          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.61/0.82             (k1_zfmisc_1 @ 
% 0.61/0.82              (u1_struct_0 @ 
% 0.61/0.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.61/0.82          | ~ (l1_pre_topc @ X0)
% 0.61/0.82          | ~ (v2_pre_topc @ X0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['34', '37'])).
% 0.61/0.82  thf('39', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (v2_pre_topc @ X0)
% 0.61/0.82          | ~ (l1_pre_topc @ X0)
% 0.61/0.82          | ~ (v2_pre_topc @ X0)
% 0.61/0.82          | ~ (l1_pre_topc @ X0)
% 0.61/0.82          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.61/0.82             (k1_zfmisc_1 @ 
% 0.61/0.82              (u1_struct_0 @ 
% 0.61/0.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.61/0.82          | ~ (l1_struct_0 @ X0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['33', '38'])).
% 0.61/0.82  thf('40', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (l1_struct_0 @ X0)
% 0.61/0.82          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.61/0.82             (k1_zfmisc_1 @ 
% 0.61/0.82              (u1_struct_0 @ 
% 0.61/0.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.61/0.82          | ~ (l1_pre_topc @ X0)
% 0.61/0.82          | ~ (v2_pre_topc @ X0))),
% 0.61/0.82      inference('simplify', [status(thm)], ['39'])).
% 0.61/0.82  thf('41', plain,
% 0.61/0.82      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.61/0.82        | ~ (v2_pre_topc @ sk_B)
% 0.61/0.82        | ~ (l1_pre_topc @ sk_B)
% 0.61/0.82        | ~ (l1_struct_0 @ sk_B))),
% 0.61/0.82      inference('sup+', [status(thm)], ['32', '40'])).
% 0.61/0.82  thf('42', plain, ((v2_pre_topc @ sk_B)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('45', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.61/0.82      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.61/0.82  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 0.61/0.82      inference('sup-', [status(thm)], ['44', '45'])).
% 0.61/0.82  thf('47', plain,
% 0.61/0.82      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.61/0.82      inference('demod', [status(thm)], ['41', '42', '43', '46'])).
% 0.61/0.82  thf('48', plain,
% 0.61/0.82      (![X5 : $i, X6 : $i]:
% 0.61/0.82         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.61/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.82  thf('49', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.61/0.82      inference('sup-', [status(thm)], ['47', '48'])).
% 0.61/0.82  thf('50', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['31', '49'])).
% 0.61/0.82  thf('51', plain,
% 0.61/0.82      (![X8 : $i]:
% 0.61/0.82         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.61/0.82  thf('52', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['31', '49'])).
% 0.61/0.82  thf('53', plain,
% 0.61/0.82      ((((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_B))),
% 0.61/0.82      inference('sup+', [status(thm)], ['51', '52'])).
% 0.61/0.82  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 0.61/0.82      inference('sup-', [status(thm)], ['44', '45'])).
% 0.61/0.82  thf('55', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['53', '54'])).
% 0.61/0.82  thf('56', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.61/0.82      inference('demod', [status(thm)], ['50', '55'])).
% 0.61/0.82  thf('57', plain,
% 0.61/0.82      (![X8 : $i]:
% 0.61/0.82         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.61/0.82  thf('58', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['53', '54'])).
% 0.61/0.82  thf('59', plain,
% 0.61/0.82      ((((k2_struct_0 @ sk_B) = (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.61/0.82      inference('sup+', [status(thm)], ['57', '58'])).
% 0.61/0.82  thf('60', plain, ((l1_struct_0 @ sk_C)),
% 0.61/0.82      inference('sup-', [status(thm)], ['20', '21'])).
% 0.61/0.82  thf('61', plain, (((k2_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['59', '60'])).
% 0.61/0.82  thf('62', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['56', '61'])).
% 0.61/0.82  thf('63', plain,
% 0.61/0.82      (((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.61/0.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.61/0.82         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('demod', [status(thm)], ['3', '4', '62'])).
% 0.61/0.82  thf('64', plain,
% 0.61/0.82      (![X8 : $i]:
% 0.61/0.82         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.61/0.82  thf(t11_tsep_1, axiom,
% 0.61/0.82    (![A:$i]:
% 0.61/0.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.82       ( ![B:$i]:
% 0.61/0.82         ( ( m1_pre_topc @ B @ A ) =>
% 0.61/0.82           ( ![C:$i]:
% 0.61/0.82             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.82               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.61/0.82                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.61/0.82                   ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.61/0.82  thf('65', plain,
% 0.61/0.82      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.82         (~ (m1_pre_topc @ X16 @ X17)
% 0.61/0.82          | ((X18) != (u1_struct_0 @ X16))
% 0.61/0.82          | ~ (v4_pre_topc @ X18 @ X17)
% 0.61/0.82          | (v1_borsuk_1 @ X16 @ X17)
% 0.61/0.82          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.61/0.82          | ~ (l1_pre_topc @ X17)
% 0.61/0.82          | ~ (v2_pre_topc @ X17))),
% 0.61/0.82      inference('cnf', [status(esa)], [t11_tsep_1])).
% 0.61/0.82  thf('66', plain,
% 0.61/0.82      (![X16 : $i, X17 : $i]:
% 0.61/0.82         (~ (v2_pre_topc @ X17)
% 0.61/0.82          | ~ (l1_pre_topc @ X17)
% 0.61/0.82          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.61/0.82               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.61/0.82          | (v1_borsuk_1 @ X16 @ X17)
% 0.61/0.82          | ~ (v4_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 0.61/0.82          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.61/0.82      inference('simplify', [status(thm)], ['65'])).
% 0.61/0.82  thf('67', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         (~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.61/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.61/0.82          | ~ (l1_struct_0 @ X0)
% 0.61/0.82          | ~ (m1_pre_topc @ X0 @ X1)
% 0.61/0.82          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X1)
% 0.61/0.82          | (v1_borsuk_1 @ X0 @ X1)
% 0.61/0.82          | ~ (l1_pre_topc @ X1)
% 0.61/0.82          | ~ (v2_pre_topc @ X1))),
% 0.61/0.82      inference('sup-', [status(thm)], ['64', '66'])).
% 0.61/0.82  thf('68', plain,
% 0.61/0.82      (((~ (v2_pre_topc @ sk_A)
% 0.61/0.82         | ~ (l1_pre_topc @ sk_A)
% 0.61/0.82         | (v1_borsuk_1 @ sk_C @ sk_A)
% 0.61/0.82         | ~ (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.61/0.82         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.61/0.82         | ~ (l1_struct_0 @ sk_C))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['63', '67'])).
% 0.61/0.82  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('71', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['53', '54'])).
% 0.61/0.82  thf('72', plain, (((k2_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['59', '60'])).
% 0.61/0.82  thf('73', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['71', '72'])).
% 0.61/0.82  thf('74', plain,
% 0.61/0.82      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('split', [status(esa)], ['0'])).
% 0.61/0.82  thf(t11_tmap_1, axiom,
% 0.61/0.82    (![A:$i]:
% 0.61/0.82     ( ( l1_pre_topc @ A ) =>
% 0.61/0.82       ( ![B:$i]:
% 0.61/0.82         ( ( m1_pre_topc @ B @ A ) =>
% 0.61/0.82           ( ( v1_pre_topc @
% 0.61/0.82               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.61/0.82             ( m1_pre_topc @
% 0.61/0.82               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.61/0.82  thf('75', plain,
% 0.61/0.82      (![X14 : $i, X15 : $i]:
% 0.61/0.82         (~ (m1_pre_topc @ X14 @ X15)
% 0.61/0.82          | (m1_pre_topc @ 
% 0.61/0.82             (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)) @ X15)
% 0.61/0.82          | ~ (l1_pre_topc @ X15))),
% 0.61/0.82      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.61/0.82  thf('76', plain,
% 0.61/0.82      (((~ (l1_pre_topc @ sk_A)
% 0.61/0.82         | (m1_pre_topc @ 
% 0.61/0.82            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)))
% 0.61/0.82         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['74', '75'])).
% 0.61/0.82  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('78', plain,
% 0.61/0.82      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('79', plain,
% 0.61/0.82      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.61/0.82  thf('80', plain, ((l1_struct_0 @ sk_C)),
% 0.61/0.82      inference('sup-', [status(thm)], ['20', '21'])).
% 0.61/0.82  thf('81', plain,
% 0.61/0.82      ((((v1_borsuk_1 @ sk_C @ sk_A)
% 0.61/0.82         | ~ (v4_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)))
% 0.61/0.82         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('demod', [status(thm)], ['68', '69', '70', '73', '79', '80'])).
% 0.61/0.82  thf('82', plain,
% 0.61/0.82      (((m1_pre_topc @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('83', plain,
% 0.61/0.82      (((m1_pre_topc @ sk_C @ sk_A)) | ((m1_pre_topc @ sk_B @ sk_A))),
% 0.61/0.82      inference('split', [status(esa)], ['82'])).
% 0.61/0.82  thf('84', plain,
% 0.61/0.82      (((m1_pre_topc @ sk_C @ sk_A) | (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('85', plain,
% 0.61/0.82      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.61/0.82      inference('split', [status(esa)], ['84'])).
% 0.61/0.82  thf('86', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['56', '61'])).
% 0.61/0.82  thf(t12_tmap_1, axiom,
% 0.61/0.82    (![A:$i]:
% 0.61/0.82     ( ( l1_pre_topc @ A ) =>
% 0.61/0.82       ( ![B:$i]:
% 0.61/0.82         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.61/0.82           ( ![C:$i]:
% 0.61/0.82             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.61/0.82               ( ( ( B ) =
% 0.61/0.82                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.61/0.82                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.61/0.82  thf('87', plain,
% 0.61/0.82      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.61/0.82         (~ (v2_pre_topc @ X19)
% 0.61/0.82          | ~ (l1_pre_topc @ X19)
% 0.61/0.82          | ((X19) != (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)))
% 0.61/0.82          | ~ (m1_pre_topc @ X19 @ X21)
% 0.61/0.82          | (m1_pre_topc @ X20 @ X21)
% 0.61/0.82          | ~ (l1_pre_topc @ X20)
% 0.61/0.82          | ~ (v2_pre_topc @ X20)
% 0.61/0.82          | ~ (l1_pre_topc @ X21))),
% 0.61/0.82      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.61/0.82  thf('88', plain,
% 0.61/0.82      (![X20 : $i, X21 : $i]:
% 0.61/0.82         (~ (l1_pre_topc @ X21)
% 0.61/0.82          | ~ (v2_pre_topc @ X20)
% 0.61/0.82          | ~ (l1_pre_topc @ X20)
% 0.61/0.82          | (m1_pre_topc @ X20 @ X21)
% 0.61/0.82          | ~ (m1_pre_topc @ 
% 0.61/0.82               (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)) @ X21)
% 0.61/0.82          | ~ (l1_pre_topc @ 
% 0.61/0.82               (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)))
% 0.61/0.82          | ~ (v2_pre_topc @ 
% 0.61/0.82               (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20))))),
% 0.61/0.82      inference('simplify', [status(thm)], ['87'])).
% 0.61/0.82  thf('89', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (l1_pre_topc @ 
% 0.61/0.82             (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))
% 0.61/0.82          | ~ (v2_pre_topc @ 
% 0.61/0.82               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.61/0.82          | ~ (m1_pre_topc @ 
% 0.61/0.82               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.61/0.82          | (m1_pre_topc @ sk_B @ X0)
% 0.61/0.82          | ~ (l1_pre_topc @ sk_B)
% 0.61/0.82          | ~ (v2_pre_topc @ sk_B)
% 0.61/0.82          | ~ (l1_pre_topc @ X0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['86', '88'])).
% 0.61/0.82  thf('90', plain,
% 0.61/0.82      (![X8 : $i]:
% 0.61/0.82         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.61/0.82  thf('91', plain,
% 0.61/0.82      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('92', plain,
% 0.61/0.82      ((((sk_C) = (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.61/0.82        | ~ (l1_struct_0 @ sk_B))),
% 0.61/0.82      inference('sup+', [status(thm)], ['90', '91'])).
% 0.61/0.82  thf('93', plain, ((l1_struct_0 @ sk_B)),
% 0.61/0.82      inference('sup-', [status(thm)], ['44', '45'])).
% 0.61/0.82  thf('94', plain,
% 0.61/0.82      (((sk_C) = (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.61/0.82      inference('demod', [status(thm)], ['92', '93'])).
% 0.61/0.82  thf('95', plain, (((k2_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['59', '60'])).
% 0.61/0.82  thf('96', plain,
% 0.61/0.82      (((sk_C) = (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))),
% 0.61/0.82      inference('demod', [status(thm)], ['94', '95'])).
% 0.61/0.82  thf('97', plain, ((l1_pre_topc @ sk_C)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('98', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['56', '61'])).
% 0.61/0.82  thf('99', plain,
% 0.61/0.82      (((sk_C) = (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))),
% 0.61/0.82      inference('demod', [status(thm)], ['94', '95'])).
% 0.61/0.82  thf('100', plain, ((v2_pre_topc @ sk_C)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('101', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['56', '61'])).
% 0.61/0.82  thf('102', plain,
% 0.61/0.82      (((sk_C) = (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))),
% 0.61/0.82      inference('demod', [status(thm)], ['94', '95'])).
% 0.61/0.82  thf('103', plain, ((l1_pre_topc @ sk_B)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('104', plain, ((v2_pre_topc @ sk_B)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('105', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (m1_pre_topc @ sk_C @ X0)
% 0.61/0.82          | (m1_pre_topc @ sk_B @ X0)
% 0.61/0.82          | ~ (l1_pre_topc @ X0))),
% 0.61/0.82      inference('demod', [status(thm)],
% 0.61/0.82                ['89', '96', '97', '98', '99', '100', '101', '102', '103', 
% 0.61/0.82                 '104'])).
% 0.61/0.82  thf('106', plain,
% 0.61/0.82      (((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A)))
% 0.61/0.82         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['85', '105'])).
% 0.61/0.82  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('108', plain,
% 0.61/0.82      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.61/0.82      inference('demod', [status(thm)], ['106', '107'])).
% 0.61/0.82  thf('109', plain,
% 0.61/0.82      ((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.61/0.82        | ~ (v1_borsuk_1 @ sk_C @ sk_A)
% 0.61/0.82        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.61/0.82        | ~ (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('110', plain,
% 0.61/0.82      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('split', [status(esa)], ['109'])).
% 0.61/0.82  thf('111', plain,
% 0.61/0.82      (((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.61/0.82      inference('sup-', [status(thm)], ['108', '110'])).
% 0.61/0.82  thf('112', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.61/0.82      inference('sat_resolution*', [status(thm)], ['83', '111'])).
% 0.61/0.82  thf('113', plain,
% 0.61/0.82      (((v1_borsuk_1 @ sk_C @ sk_A)
% 0.61/0.82        | ~ (v4_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A))),
% 0.61/0.82      inference('simpl_trail', [status(thm)], ['81', '112'])).
% 0.61/0.82  thf('114', plain,
% 0.61/0.82      ((~ (v1_borsuk_1 @ sk_C @ sk_A)) <= (~ ((v1_borsuk_1 @ sk_C @ sk_A)))),
% 0.61/0.82      inference('split', [status(esa)], ['109'])).
% 0.61/0.82  thf('115', plain,
% 0.61/0.82      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.61/0.82  thf('116', plain,
% 0.61/0.82      ((~ (m1_pre_topc @ sk_C @ sk_A)) <= (~ ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.61/0.82      inference('split', [status(esa)], ['109'])).
% 0.61/0.82  thf('117', plain,
% 0.61/0.82      (((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.61/0.82      inference('sup-', [status(thm)], ['115', '116'])).
% 0.61/0.82  thf('118', plain,
% 0.61/0.82      (~ ((v1_borsuk_1 @ sk_C @ sk_A)) | ~ ((v1_borsuk_1 @ sk_B @ sk_A)) | 
% 0.61/0.82       ~ ((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.61/0.82      inference('split', [status(esa)], ['109'])).
% 0.61/0.82  thf('119', plain,
% 0.61/0.82      (((v1_borsuk_1 @ sk_C @ sk_A) | (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('120', plain,
% 0.61/0.82      (((v1_borsuk_1 @ sk_C @ sk_A)) <= (((v1_borsuk_1 @ sk_C @ sk_A)))),
% 0.61/0.82      inference('split', [status(esa)], ['119'])).
% 0.61/0.82  thf('121', plain,
% 0.61/0.82      (((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.61/0.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.61/0.82         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('demod', [status(thm)], ['3', '4', '62'])).
% 0.61/0.82  thf('122', plain,
% 0.61/0.82      (![X8 : $i]:
% 0.61/0.82         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.61/0.82  thf('123', plain,
% 0.61/0.82      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.82         (~ (m1_pre_topc @ X16 @ X17)
% 0.61/0.82          | ((X18) != (u1_struct_0 @ X16))
% 0.61/0.82          | ~ (v1_borsuk_1 @ X16 @ X17)
% 0.61/0.82          | ~ (m1_pre_topc @ X16 @ X17)
% 0.61/0.82          | (v4_pre_topc @ X18 @ X17)
% 0.61/0.82          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.61/0.82          | ~ (l1_pre_topc @ X17)
% 0.61/0.82          | ~ (v2_pre_topc @ X17))),
% 0.61/0.82      inference('cnf', [status(esa)], [t11_tsep_1])).
% 0.61/0.82  thf('124', plain,
% 0.61/0.82      (![X16 : $i, X17 : $i]:
% 0.61/0.82         (~ (v2_pre_topc @ X17)
% 0.61/0.82          | ~ (l1_pre_topc @ X17)
% 0.61/0.82          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.61/0.82               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.61/0.82          | (v4_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 0.61/0.82          | ~ (v1_borsuk_1 @ X16 @ X17)
% 0.61/0.82          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.61/0.82      inference('simplify', [status(thm)], ['123'])).
% 0.61/0.82  thf('125', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         (~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.61/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.61/0.82          | ~ (l1_struct_0 @ X0)
% 0.61/0.82          | ~ (m1_pre_topc @ X0 @ X1)
% 0.61/0.82          | ~ (v1_borsuk_1 @ X0 @ X1)
% 0.61/0.82          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X1)
% 0.61/0.82          | ~ (l1_pre_topc @ X1)
% 0.61/0.82          | ~ (v2_pre_topc @ X1))),
% 0.61/0.82      inference('sup-', [status(thm)], ['122', '124'])).
% 0.61/0.82  thf('126', plain,
% 0.61/0.82      (((~ (v2_pre_topc @ sk_A)
% 0.61/0.82         | ~ (l1_pre_topc @ sk_A)
% 0.61/0.82         | (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.61/0.82         | ~ (v1_borsuk_1 @ sk_C @ sk_A)
% 0.61/0.82         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.61/0.82         | ~ (l1_struct_0 @ sk_C))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['121', '125'])).
% 0.61/0.82  thf('127', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('129', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['71', '72'])).
% 0.61/0.82  thf('130', plain,
% 0.61/0.82      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.61/0.82  thf('131', plain, ((l1_struct_0 @ sk_C)),
% 0.61/0.82      inference('sup-', [status(thm)], ['20', '21'])).
% 0.61/0.82  thf('132', plain,
% 0.61/0.82      ((((v4_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)
% 0.61/0.82         | ~ (v1_borsuk_1 @ sk_C @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('demod', [status(thm)],
% 0.61/0.82                ['126', '127', '128', '129', '130', '131'])).
% 0.61/0.82  thf('133', plain,
% 0.61/0.82      (((v4_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A))
% 0.61/0.82         <= (((v1_borsuk_1 @ sk_C @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['120', '132'])).
% 0.61/0.82  thf('134', plain,
% 0.61/0.82      (((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.61/0.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.61/0.82         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('demod', [status(thm)], ['3', '4', '62'])).
% 0.61/0.82  thf('135', plain, (((k2_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['59', '60'])).
% 0.61/0.82  thf('136', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         (~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.61/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.61/0.82          | ~ (l1_struct_0 @ X0)
% 0.61/0.82          | ~ (m1_pre_topc @ X0 @ X1)
% 0.61/0.82          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X1)
% 0.61/0.82          | (v1_borsuk_1 @ X0 @ X1)
% 0.61/0.82          | ~ (l1_pre_topc @ X1)
% 0.61/0.82          | ~ (v2_pre_topc @ X1))),
% 0.61/0.82      inference('sup-', [status(thm)], ['64', '66'])).
% 0.61/0.82  thf('137', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.61/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.61/0.82          | ~ (v2_pre_topc @ X0)
% 0.61/0.82          | ~ (l1_pre_topc @ X0)
% 0.61/0.82          | (v1_borsuk_1 @ sk_B @ X0)
% 0.61/0.82          | ~ (v4_pre_topc @ (u1_struct_0 @ sk_B) @ X0)
% 0.61/0.82          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.61/0.82          | ~ (l1_struct_0 @ sk_B))),
% 0.61/0.82      inference('sup-', [status(thm)], ['135', '136'])).
% 0.61/0.82  thf('138', plain, ((l1_struct_0 @ sk_B)),
% 0.61/0.82      inference('sup-', [status(thm)], ['44', '45'])).
% 0.61/0.82  thf('139', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.61/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.61/0.82          | ~ (v2_pre_topc @ X0)
% 0.61/0.82          | ~ (l1_pre_topc @ X0)
% 0.61/0.82          | (v1_borsuk_1 @ sk_B @ X0)
% 0.61/0.82          | ~ (v4_pre_topc @ (u1_struct_0 @ sk_B) @ X0)
% 0.61/0.82          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.61/0.82      inference('demod', [status(thm)], ['137', '138'])).
% 0.61/0.82  thf('140', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['56', '61'])).
% 0.61/0.82  thf('141', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.61/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.61/0.82          | ~ (v2_pre_topc @ X0)
% 0.61/0.82          | ~ (l1_pre_topc @ X0)
% 0.61/0.82          | (v1_borsuk_1 @ sk_B @ X0)
% 0.61/0.82          | ~ (v4_pre_topc @ (k2_struct_0 @ sk_C) @ X0)
% 0.61/0.82          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.61/0.82      inference('demod', [status(thm)], ['139', '140'])).
% 0.61/0.82  thf('142', plain,
% 0.61/0.82      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.61/0.82         | ~ (v4_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)
% 0.61/0.82         | (v1_borsuk_1 @ sk_B @ sk_A)
% 0.61/0.82         | ~ (l1_pre_topc @ sk_A)
% 0.61/0.82         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['134', '141'])).
% 0.61/0.82  thf('143', plain,
% 0.61/0.82      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('split', [status(esa)], ['0'])).
% 0.61/0.82  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('145', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('146', plain,
% 0.61/0.82      (((~ (v4_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)
% 0.61/0.82         | (v1_borsuk_1 @ sk_B @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 0.61/0.82  thf('147', plain,
% 0.61/0.82      (((v1_borsuk_1 @ sk_B @ sk_A))
% 0.61/0.82         <= (((v1_borsuk_1 @ sk_C @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['133', '146'])).
% 0.61/0.82  thf('148', plain,
% 0.61/0.82      ((~ (v1_borsuk_1 @ sk_B @ sk_A)) <= (~ ((v1_borsuk_1 @ sk_B @ sk_A)))),
% 0.61/0.82      inference('split', [status(esa)], ['109'])).
% 0.61/0.82  thf('149', plain,
% 0.61/0.82      (((v1_borsuk_1 @ sk_B @ sk_A)) | ~ ((v1_borsuk_1 @ sk_C @ sk_A)) | 
% 0.61/0.82       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.61/0.82      inference('sup-', [status(thm)], ['147', '148'])).
% 0.61/0.82  thf('150', plain, (~ ((v1_borsuk_1 @ sk_C @ sk_A))),
% 0.61/0.82      inference('sat_resolution*', [status(thm)],
% 0.61/0.82                ['117', '118', '83', '111', '149'])).
% 0.61/0.82  thf('151', plain, (~ (v1_borsuk_1 @ sk_C @ sk_A)),
% 0.61/0.82      inference('simpl_trail', [status(thm)], ['114', '150'])).
% 0.61/0.82  thf('152', plain, (~ (v4_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)),
% 0.61/0.82      inference('clc', [status(thm)], ['113', '151'])).
% 0.61/0.82  thf('153', plain,
% 0.61/0.82      (((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.61/0.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.61/0.82         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('demod', [status(thm)], ['3', '4', '62'])).
% 0.61/0.82  thf('154', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.61/0.82      inference('sat_resolution*', [status(thm)], ['83', '111'])).
% 0.61/0.82  thf('155', plain,
% 0.61/0.82      ((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.61/0.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.82      inference('simpl_trail', [status(thm)], ['153', '154'])).
% 0.61/0.82  thf('156', plain, (((k2_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['59', '60'])).
% 0.61/0.82  thf('157', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         (~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.61/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.61/0.82          | ~ (l1_struct_0 @ X0)
% 0.61/0.82          | ~ (m1_pre_topc @ X0 @ X1)
% 0.61/0.82          | ~ (v1_borsuk_1 @ X0 @ X1)
% 0.61/0.82          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X1)
% 0.61/0.82          | ~ (l1_pre_topc @ X1)
% 0.61/0.82          | ~ (v2_pre_topc @ X1))),
% 0.61/0.82      inference('sup-', [status(thm)], ['122', '124'])).
% 0.61/0.82  thf('158', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.61/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.61/0.82          | ~ (v2_pre_topc @ X0)
% 0.61/0.82          | ~ (l1_pre_topc @ X0)
% 0.61/0.82          | (v4_pre_topc @ (u1_struct_0 @ sk_B) @ X0)
% 0.61/0.82          | ~ (v1_borsuk_1 @ sk_B @ X0)
% 0.61/0.82          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.61/0.82          | ~ (l1_struct_0 @ sk_B))),
% 0.61/0.82      inference('sup-', [status(thm)], ['156', '157'])).
% 0.61/0.82  thf('159', plain, ((l1_struct_0 @ sk_B)),
% 0.61/0.82      inference('sup-', [status(thm)], ['44', '45'])).
% 0.61/0.82  thf('160', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.61/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.61/0.82          | ~ (v2_pre_topc @ X0)
% 0.61/0.82          | ~ (l1_pre_topc @ X0)
% 0.61/0.82          | (v4_pre_topc @ (u1_struct_0 @ sk_B) @ X0)
% 0.61/0.82          | ~ (v1_borsuk_1 @ sk_B @ X0)
% 0.61/0.82          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.61/0.82      inference('demod', [status(thm)], ['158', '159'])).
% 0.61/0.82  thf('161', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.61/0.82      inference('demod', [status(thm)], ['56', '61'])).
% 0.61/0.82  thf('162', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.61/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.61/0.82          | ~ (v2_pre_topc @ X0)
% 0.61/0.82          | ~ (l1_pre_topc @ X0)
% 0.61/0.82          | (v4_pre_topc @ (k2_struct_0 @ sk_C) @ X0)
% 0.61/0.82          | ~ (v1_borsuk_1 @ sk_B @ X0)
% 0.61/0.82          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.61/0.82      inference('demod', [status(thm)], ['160', '161'])).
% 0.61/0.82  thf('163', plain,
% 0.61/0.82      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.61/0.82        | ~ (v1_borsuk_1 @ sk_B @ sk_A)
% 0.61/0.82        | (v4_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)
% 0.61/0.82        | ~ (l1_pre_topc @ sk_A)
% 0.61/0.82        | ~ (v2_pre_topc @ sk_A))),
% 0.61/0.82      inference('sup-', [status(thm)], ['155', '162'])).
% 0.61/0.82  thf('164', plain,
% 0.61/0.82      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.82      inference('split', [status(esa)], ['0'])).
% 0.61/0.82  thf('165', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.61/0.82      inference('sat_resolution*', [status(thm)], ['83', '111'])).
% 0.61/0.82  thf('166', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.61/0.82      inference('simpl_trail', [status(thm)], ['164', '165'])).
% 0.61/0.82  thf('167', plain,
% 0.61/0.82      (((v1_borsuk_1 @ sk_B @ sk_A)) <= (((v1_borsuk_1 @ sk_B @ sk_A)))),
% 0.61/0.82      inference('split', [status(esa)], ['119'])).
% 0.61/0.82  thf('168', plain,
% 0.61/0.82      (((v1_borsuk_1 @ sk_B @ sk_A)) | ((v1_borsuk_1 @ sk_C @ sk_A))),
% 0.61/0.82      inference('split', [status(esa)], ['119'])).
% 0.61/0.82  thf('169', plain, (((v1_borsuk_1 @ sk_B @ sk_A))),
% 0.61/0.82      inference('sat_resolution*', [status(thm)],
% 0.61/0.82                ['117', '118', '83', '111', '149', '168'])).
% 0.61/0.82  thf('170', plain, ((v1_borsuk_1 @ sk_B @ sk_A)),
% 0.61/0.82      inference('simpl_trail', [status(thm)], ['167', '169'])).
% 0.61/0.82  thf('171', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('172', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('173', plain, ((v4_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)),
% 0.61/0.82      inference('demod', [status(thm)], ['163', '166', '170', '171', '172'])).
% 0.61/0.82  thf('174', plain, ($false), inference('demod', [status(thm)], ['152', '173'])).
% 0.61/0.82  
% 0.61/0.82  % SZS output end Refutation
% 0.61/0.82  
% 0.61/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
