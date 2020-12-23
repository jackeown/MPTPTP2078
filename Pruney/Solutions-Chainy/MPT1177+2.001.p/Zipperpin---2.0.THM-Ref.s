%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q6RureokO8

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  157 (1431 expanded)
%              Number of leaves         :   34 ( 420 expanded)
%              Depth                    :   27
%              Number of atoms          : 1196 (26683 expanded)
%              Number of equality atoms :   31 ( 125 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(t84_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ( ( r2_xboole_0 @ C @ D )
                  <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m2_orders_2 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m2_orders_2 @ D @ A @ B )
                   => ( ( r2_xboole_0 @ C @ D )
                    <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_orders_2])).

thf('0',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
    | ( r2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D_1 )
   <= ( r2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
    | ~ ( r2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
    | ~ ( r2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,(
    m2_orders_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_orders_2 @ C @ A @ B )
         => ( ( v6_orders_2 @ C @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_orders_1 @ X11 @ ( k1_orders_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m2_orders_2 @ X12 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf(t67_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_orders_2 @ C @ A @ B )
             => ( r1_tarski @ C @ B ) ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ X15 @ X13 )
      | ~ ( m1_orders_2 @ X15 @ X14 @ X13 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 )
      | ( r1_tarski @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 )
      | ( r1_tarski @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_D_1 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ sk_C @ sk_D_1 )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('29',plain,
    ( ( ( sk_C = sk_D_1 )
      | ( r2_xboole_0 @ sk_C @ sk_D_1 ) )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
   <= ~ ( r2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('31',plain,
    ( ( sk_C = sk_D_1 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_C )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t68_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ~ ( ( B != k1_xboole_0 )
                & ( m1_orders_2 @ B @ A @ B ) )
            & ~ ( ~ ( m1_orders_2 @ B @ A @ B )
                & ( B = k1_xboole_0 ) ) ) ) ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_orders_2 @ X16 @ X17 @ X16 )
      | ( X16 = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t68_orders_2])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['33','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('48',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(d16_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v6_orders_2 @ C @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( m2_orders_2 @ C @ A @ B )
              <=> ( ( C != k1_xboole_0 )
                  & ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ C )
                       => ( ( k1_funct_1 @ B @ ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) )
                          = D ) ) ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_orders_1 @ X6 @ ( k1_orders_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m2_orders_2 @ X8 @ X7 @ X6 )
      | ( X8 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v6_orders_2 @ X8 @ X7 )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d16_orders_2])).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ X7 @ X6 )
      | ~ ( m1_orders_1 @ X6 @ ( k1_orders_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
        | ~ ( v6_orders_2 @ k1_xboole_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['33','45'])).

thf('53',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_orders_1 @ X11 @ ( k1_orders_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v6_orders_2 @ X12 @ X10 )
      | ~ ( m2_orders_2 @ X12 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v6_orders_2 @ X0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    v6_orders_2 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['53','63'])).

thf('65',plain,
    ( ( v6_orders_2 @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['52','64'])).

thf('66',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['51','65','66','67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
        | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','72'])).

thf('74',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['33','45'])).

thf('75',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D_1 )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D_1 )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,(
    r2_xboole_0 @ sk_C @ sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['3','77','78'])).

thf('80',plain,(
    r2_xboole_0 @ sk_C @ sk_D_1 ),
    inference(simpl_trail,[status(thm)],['1','79'])).

thf('81',plain,(
    m2_orders_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ( ( C != D )
                   => ( ( m1_orders_2 @ C @ A @ D )
                    <=> ~ ( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) )).

thf('84',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_orders_1 @ X18 @ ( k1_orders_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m2_orders_2 @ X20 @ X19 @ X18 )
      | ( m1_orders_2 @ X20 @ X19 @ X21 )
      | ( m1_orders_2 @ X21 @ X19 @ X20 )
      | ( X21 = X20 )
      | ~ ( m2_orders_2 @ X21 @ X19 @ X18 )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ( sk_C = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D_1 )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
    | ( m1_orders_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['81','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('94',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ X15 @ X13 )
      | ~ ( m1_orders_2 @ X15 @ X14 @ X13 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
    | ( sk_C = sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['92','102'])).

thf('104',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('105',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','77'])).

thf('106',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D_1 ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D_1 )
   <= ( r2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('110',plain,
    ( ( r1_tarski @ sk_C @ sk_D_1 )
   <= ( r2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('111',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('112',plain,
    ( ( ~ ( r1_tarski @ sk_D_1 @ sk_C )
      | ( sk_D_1 = sk_C ) )
   <= ( r2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    r2_xboole_0 @ sk_C @ sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['3','77','78'])).

thf('114',plain,
    ( ~ ( r1_tarski @ sk_D_1 @ sk_C )
    | ( sk_D_1 = sk_C ) ),
    inference(simpl_trail,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( sk_C = sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['107','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    sk_C = sk_D_1 ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['80','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('120',plain,(
    ! [X1: $i] :
      ~ ( r2_xboole_0 @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    $false ),
    inference('sup-',[status(thm)],['118','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q6RureokO8
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:11:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 104 iterations in 0.050s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.20/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.52  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.20/0.52  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.20/0.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.52  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.20/0.52  thf(t84_orders_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.52                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.52                  ( ![D:$i]:
% 0.20/0.52                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.52                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1) | (r2_xboole_0 @ sk_C @ sk_D_1))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (((r2_xboole_0 @ sk_C @ sk_D_1)) <= (((r2_xboole_0 @ sk_C @ sk_D_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D_1)
% 0.20/0.52        | ~ (r2_xboole_0 @ sk_C @ sk_D_1))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)) | 
% 0.20/0.52       ~ ((r2_xboole_0 @ sk_C @ sk_D_1))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1))
% 0.20/0.52         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('6', plain, ((m2_orders_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_m2_orders_2, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.52         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.52           ( ( v6_orders_2 @ C @ A ) & 
% 0.20/0.52             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.52         (~ (l1_orders_2 @ X10)
% 0.20/0.52          | ~ (v5_orders_2 @ X10)
% 0.20/0.52          | ~ (v4_orders_2 @ X10)
% 0.20/0.52          | ~ (v3_orders_2 @ X10)
% 0.20/0.52          | (v2_struct_0 @ X10)
% 0.20/0.52          | ~ (m1_orders_1 @ X11 @ (k1_orders_1 @ (u1_struct_0 @ X10)))
% 0.20/0.52          | (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.52          | ~ (m2_orders_2 @ X12 @ X10 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('11', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('12', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('13', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.20/0.52  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '16'])).
% 0.20/0.52  thf(t67_orders_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.52          | (r1_tarski @ X15 @ X13)
% 0.20/0.52          | ~ (m1_orders_2 @ X15 @ X14 @ X13)
% 0.20/0.52          | ~ (l1_orders_2 @ X14)
% 0.20/0.52          | ~ (v5_orders_2 @ X14)
% 0.20/0.52          | ~ (v4_orders_2 @ X14)
% 0.20/0.52          | ~ (v3_orders_2 @ X14)
% 0.20/0.52          | (v2_struct_0 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.20/0.52          | (r1_tarski @ X0 @ sk_D_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('21', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('22', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.20/0.52          | (r1_tarski @ X0 @ sk_D_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.20/0.52  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ X0 @ sk_D_1) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1))),
% 0.20/0.52      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (((r1_tarski @ sk_C @ sk_D_1))
% 0.20/0.52         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '26'])).
% 0.20/0.52  thf(d8_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.52       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i, X2 : $i]:
% 0.20/0.52         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((((sk_C) = (sk_D_1)) | (r2_xboole_0 @ sk_C @ sk_D_1)))
% 0.20/0.52         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      ((~ (r2_xboole_0 @ sk_C @ sk_D_1)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      ((((sk_C) = (sk_D_1)))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1))
% 0.20/0.52         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('34', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf(t68_orders_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( m1_orders_2 @ B @ A @ B ) ) ) & 
% 0.20/0.52             ( ~( ( ~( m1_orders_2 @ B @ A @ B ) ) & 
% 0.20/0.52                  ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.52          | ~ (m1_orders_2 @ X16 @ X17 @ X16)
% 0.20/0.52          | ((X16) = (k1_xboole_0))
% 0.20/0.52          | ~ (l1_orders_2 @ X17)
% 0.20/0.52          | ~ (v5_orders_2 @ X17)
% 0.20/0.52          | ~ (v4_orders_2 @ X17)
% 0.20/0.52          | ~ (v3_orders_2 @ X17)
% 0.20/0.52          | (v2_struct_0 @ X17))),
% 0.20/0.52      inference('cnf', [status(esa)], [t68_orders_2])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.52        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.52        | ((sk_C) = (k1_xboole_0))
% 0.20/0.52        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((sk_C) = (k1_xboole_0))
% 0.20/0.52        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.20/0.52  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_C) | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.52      inference('clc', [status(thm)], ['43', '44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      ((((sk_C) = (k1_xboole_0)))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf(d16_orders_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( v6_orders_2 @ C @ A ) & 
% 0.20/0.52                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52               ( ( m2_orders_2 @ C @ A @ B ) <=>
% 0.20/0.52                 ( ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52                   ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C ) & 
% 0.20/0.52                   ( ![D:$i]:
% 0.20/0.52                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52                       ( ( r2_hidden @ D @ C ) =>
% 0.20/0.52                         ( ( k1_funct_1 @
% 0.20/0.52                             B @ 
% 0.20/0.52                             ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) ) =
% 0.20/0.52                           ( D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.52         (~ (m1_orders_1 @ X6 @ (k1_orders_1 @ (u1_struct_0 @ X7)))
% 0.20/0.52          | ~ (m2_orders_2 @ X8 @ X7 @ X6)
% 0.20/0.52          | ((X8) != (k1_xboole_0))
% 0.20/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.52          | ~ (v6_orders_2 @ X8 @ X7)
% 0.20/0.52          | ~ (l1_orders_2 @ X7)
% 0.20/0.52          | ~ (v5_orders_2 @ X7)
% 0.20/0.52          | ~ (v4_orders_2 @ X7)
% 0.20/0.52          | ~ (v3_orders_2 @ X7)
% 0.20/0.52          | (v2_struct_0 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [d16_orders_2])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X7)
% 0.20/0.52          | ~ (v3_orders_2 @ X7)
% 0.20/0.52          | ~ (v4_orders_2 @ X7)
% 0.20/0.52          | ~ (v5_orders_2 @ X7)
% 0.20/0.52          | ~ (l1_orders_2 @ X7)
% 0.20/0.52          | ~ (v6_orders_2 @ k1_xboole_0 @ X7)
% 0.20/0.52          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.52          | ~ (m2_orders_2 @ k1_xboole_0 @ X7 @ X6)
% 0.20/0.52          | ~ (m1_orders_1 @ X6 @ (k1_orders_1 @ (u1_struct_0 @ X7))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52           | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.20/0.52           | ~ (v6_orders_2 @ k1_xboole_0 @ sk_A)
% 0.20/0.52           | ~ (l1_orders_2 @ sk_A)
% 0.20/0.52           | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52           | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52           | ~ (v3_orders_2 @ sk_A)
% 0.20/0.52           | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['48', '50'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      ((((sk_C) = (k1_xboole_0)))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '45'])).
% 0.20/0.52  thf('53', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.52         (~ (l1_orders_2 @ X10)
% 0.20/0.52          | ~ (v5_orders_2 @ X10)
% 0.20/0.52          | ~ (v4_orders_2 @ X10)
% 0.20/0.52          | ~ (v3_orders_2 @ X10)
% 0.20/0.52          | (v2_struct_0 @ X10)
% 0.20/0.52          | ~ (m1_orders_1 @ X11 @ (k1_orders_1 @ (u1_struct_0 @ X10)))
% 0.20/0.52          | (v6_orders_2 @ X12 @ X10)
% 0.20/0.52          | ~ (m2_orders_2 @ X12 @ X10 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | (v6_orders_2 @ X0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.52  thf('57', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('58', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('59', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('60', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | (v6_orders_2 @ X0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 0.20/0.52  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v6_orders_2 @ X0 @ sk_A) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['61', '62'])).
% 0.20/0.52  thf('64', plain, ((v6_orders_2 @ sk_C @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['53', '63'])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      (((v6_orders_2 @ k1_xboole_0 @ sk_A))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['52', '64'])).
% 0.20/0.52  thf('66', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('67', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('68', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('69', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52           | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.20/0.52           | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('demod', [status(thm)], ['51', '65', '66', '67', '68', '69'])).
% 0.20/0.52  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.20/0.52           | ~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('clc', [status(thm)], ['70', '71'])).
% 0.20/0.52  thf('73', plain,
% 0.20/0.52      ((~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '72'])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      ((((sk_C) = (k1_xboole_0)))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '45'])).
% 0.20/0.52  thf('75', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('76', plain,
% 0.20/0.52      (((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['74', '75'])).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      (((r2_xboole_0 @ sk_C @ sk_D_1)) | 
% 0.20/0.52       ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['73', '76'])).
% 0.20/0.52  thf('78', plain,
% 0.20/0.52      (((r2_xboole_0 @ sk_C @ sk_D_1)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('79', plain, (((r2_xboole_0 @ sk_C @ sk_D_1))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['3', '77', '78'])).
% 0.20/0.52  thf('80', plain, ((r2_xboole_0 @ sk_C @ sk_D_1)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['1', '79'])).
% 0.20/0.52  thf('81', plain, ((m2_orders_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('82', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('83', plain,
% 0.20/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t83_orders_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.52                   ( ( ( C ) != ( D ) ) =>
% 0.20/0.52                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.20/0.52                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('84', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.52         (~ (m1_orders_1 @ X18 @ (k1_orders_1 @ (u1_struct_0 @ X19)))
% 0.20/0.52          | ~ (m2_orders_2 @ X20 @ X19 @ X18)
% 0.20/0.52          | (m1_orders_2 @ X20 @ X19 @ X21)
% 0.20/0.52          | (m1_orders_2 @ X21 @ X19 @ X20)
% 0.20/0.52          | ((X21) = (X20))
% 0.20/0.52          | ~ (m2_orders_2 @ X21 @ X19 @ X18)
% 0.20/0.52          | ~ (l1_orders_2 @ X19)
% 0.20/0.52          | ~ (v5_orders_2 @ X19)
% 0.20/0.52          | ~ (v4_orders_2 @ X19)
% 0.20/0.52          | ~ (v3_orders_2 @ X19)
% 0.20/0.52          | (v2_struct_0 @ X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.20/0.52  thf('85', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | ((X0) = (X1))
% 0.20/0.52          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.20/0.52          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.20/0.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.52  thf('86', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('87', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('88', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('90', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | ((X0) = (X1))
% 0.20/0.52          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.20/0.52          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.20/0.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['85', '86', '87', '88', '89'])).
% 0.20/0.52  thf('91', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.52          | (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.20/0.52          | ((sk_C) = (X0))
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['82', '90'])).
% 0.20/0.52  thf('92', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((sk_C) = (sk_D_1))
% 0.20/0.52        | (m1_orders_2 @ sk_C @ sk_A @ sk_D_1)
% 0.20/0.52        | (m1_orders_2 @ sk_D_1 @ sk_A @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['81', '91'])).
% 0.20/0.52  thf('93', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('94', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.52          | (r1_tarski @ X15 @ X13)
% 0.20/0.52          | ~ (m1_orders_2 @ X15 @ X14 @ X13)
% 0.20/0.52          | ~ (l1_orders_2 @ X14)
% 0.20/0.52          | ~ (v5_orders_2 @ X14)
% 0.20/0.52          | ~ (v4_orders_2 @ X14)
% 0.20/0.52          | ~ (v3_orders_2 @ X14)
% 0.20/0.52          | (v2_struct_0 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.20/0.52  thf('95', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.52          | (r1_tarski @ X0 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.52  thf('96', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('97', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('98', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('99', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('100', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.52          | (r1_tarski @ X0 @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 0.20/0.52  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('102', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.20/0.52      inference('clc', [status(thm)], ['100', '101'])).
% 0.20/0.52  thf('103', plain,
% 0.20/0.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)
% 0.20/0.52        | ((sk_C) = (sk_D_1))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | (r1_tarski @ sk_D_1 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['92', '102'])).
% 0.20/0.52  thf('104', plain,
% 0.20/0.52      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D_1))
% 0.20/0.52         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('105', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['3', '77'])).
% 0.20/0.52  thf('106', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D_1)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['104', '105'])).
% 0.20/0.52  thf('107', plain,
% 0.20/0.52      (((r1_tarski @ sk_D_1 @ sk_C)
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ((sk_C) = (sk_D_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['103', '106'])).
% 0.20/0.52  thf('108', plain,
% 0.20/0.52      (((r2_xboole_0 @ sk_C @ sk_D_1)) <= (((r2_xboole_0 @ sk_C @ sk_D_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('109', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.52  thf('110', plain,
% 0.20/0.52      (((r1_tarski @ sk_C @ sk_D_1)) <= (((r2_xboole_0 @ sk_C @ sk_D_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('111', plain,
% 0.20/0.52      (![X3 : $i, X5 : $i]:
% 0.20/0.52         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('112', plain,
% 0.20/0.52      (((~ (r1_tarski @ sk_D_1 @ sk_C) | ((sk_D_1) = (sk_C))))
% 0.20/0.52         <= (((r2_xboole_0 @ sk_C @ sk_D_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['110', '111'])).
% 0.20/0.52  thf('113', plain, (((r2_xboole_0 @ sk_C @ sk_D_1))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['3', '77', '78'])).
% 0.20/0.52  thf('114', plain, ((~ (r1_tarski @ sk_D_1 @ sk_C) | ((sk_D_1) = (sk_C)))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['112', '113'])).
% 0.20/0.52  thf('115', plain, ((((sk_C) = (sk_D_1)) | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['107', '114'])).
% 0.20/0.52  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('117', plain, (((sk_C) = (sk_D_1))),
% 0.20/0.52      inference('clc', [status(thm)], ['115', '116'])).
% 0.20/0.52  thf('118', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['80', '117'])).
% 0.20/0.52  thf('119', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (((X0) != (X1)) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.52  thf('120', plain, (![X1 : $i]: ~ (r2_xboole_0 @ X1 @ X1)),
% 0.20/0.52      inference('simplify', [status(thm)], ['119'])).
% 0.20/0.52  thf('121', plain, ($false), inference('sup-', [status(thm)], ['118', '120'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
