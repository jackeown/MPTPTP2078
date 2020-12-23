%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aCud8oTShz

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  153 (1428 expanded)
%              Number of leaves         :   34 ( 419 expanded)
%              Depth                    :   28
%              Number of atoms          : 1164 (26651 expanded)
%              Number of equality atoms :   28 ( 121 expanded)
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

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

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

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_orders_1 @ X10 @ ( k1_orders_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m2_orders_2 @ X11 @ X9 @ X10 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_orders_2 @ X14 @ X13 @ X12 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_orders_2 @ X15 @ X16 @ X15 )
      | ( X15 = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_orders_1 @ X5 @ ( k1_orders_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m2_orders_2 @ X7 @ X6 @ X5 )
      | ( X7 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v6_orders_2 @ X7 @ X6 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v3_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d16_orders_2])).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v3_orders_2 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ X6 @ X5 )
      | ~ ( m1_orders_1 @ X5 @ ( k1_orders_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_orders_1 @ X10 @ ( k1_orders_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v6_orders_2 @ X11 @ X9 )
      | ~ ( m2_orders_2 @ X11 @ X9 @ X10 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_orders_1 @ X17 @ ( k1_orders_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m2_orders_2 @ X19 @ X18 @ X17 )
      | ( m1_orders_2 @ X19 @ X18 @ X20 )
      | ( m1_orders_2 @ X20 @ X18 @ X19 )
      | ( X20 = X19 )
      | ~ ( m2_orders_2 @ X20 @ X18 @ X17 )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_orders_2 @ X14 @ X13 @ X12 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( sk_C = sk_D_1 )
    | ( r1_tarski @ sk_D_1 @ sk_C ) ),
    inference(clc,[status(thm)],['107','108'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('110',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r2_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('111',plain,
    ( ( sk_C = sk_D_1 )
    | ~ ( r2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    r2_xboole_0 @ sk_C @ sk_D_1 ),
    inference(simpl_trail,[status(thm)],['1','79'])).

thf('113',plain,(
    sk_C = sk_D_1 ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['80','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('116',plain,(
    ! [X1: $i] :
      ~ ( r2_xboole_0 @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    $false ),
    inference('sup-',[status(thm)],['114','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aCud8oTShz
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 104 iterations in 0.033s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.21/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.49  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.21/0.49  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.21/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.49  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.49  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.21/0.49  thf(t84_orders_2, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.21/0.49                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.49            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.49                  ( ![D:$i]:
% 0.21/0.49                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.21/0.49                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1) | (r2_xboole_0 @ sk_C @ sk_D_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (((r2_xboole_0 @ sk_C @ sk_D_1)) <= (((r2_xboole_0 @ sk_C @ sk_D_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D_1)
% 0.21/0.49        | ~ (r2_xboole_0 @ sk_C @ sk_D_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)) | 
% 0.21/0.49       ~ ((r2_xboole_0 @ sk_C @ sk_D_1))),
% 0.21/0.49      inference('split', [status(esa)], ['2'])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1))
% 0.21/0.49         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('6', plain, ((m2_orders_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_m2_orders_2, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.49         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.49           ( ( v6_orders_2 @ C @ A ) & 
% 0.21/0.49             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (l1_orders_2 @ X9)
% 0.21/0.49          | ~ (v5_orders_2 @ X9)
% 0.21/0.49          | ~ (v4_orders_2 @ X9)
% 0.21/0.49          | ~ (v3_orders_2 @ X9)
% 0.21/0.49          | (v2_struct_0 @ X9)
% 0.21/0.49          | ~ (m1_orders_1 @ X10 @ (k1_orders_1 @ (u1_struct_0 @ X9)))
% 0.21/0.49          | (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.49          | ~ (m2_orders_2 @ X11 @ X9 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.49          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('13', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.21/0.49  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '16'])).
% 0.21/0.49  thf(t67_orders_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.49          | (r1_tarski @ X14 @ X12)
% 0.21/0.49          | ~ (m1_orders_2 @ X14 @ X13 @ X12)
% 0.21/0.49          | ~ (l1_orders_2 @ X13)
% 0.21/0.49          | ~ (v5_orders_2 @ X13)
% 0.21/0.49          | ~ (v4_orders_2 @ X13)
% 0.21/0.49          | ~ (v3_orders_2 @ X13)
% 0.21/0.49          | (v2_struct_0 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.21/0.49          | (r1_tarski @ X0 @ sk_D_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.21/0.49          | (r1_tarski @ X0 @ sk_D_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.21/0.49  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_tarski @ X0 @ sk_D_1) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1))),
% 0.21/0.49      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (((r1_tarski @ sk_C @ sk_D_1))
% 0.21/0.49         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '26'])).
% 0.21/0.49  thf(d8_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.49       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i, X2 : $i]:
% 0.21/0.49         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((((sk_C) = (sk_D_1)) | (r2_xboole_0 @ sk_C @ sk_D_1)))
% 0.21/0.49         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((~ (r2_xboole_0 @ sk_C @ sk_D_1)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['2'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      ((((sk_C) = (sk_D_1)))
% 0.21/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.21/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1))
% 0.21/0.49         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 0.21/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.21/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf(t68_orders_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( m1_orders_2 @ B @ A @ B ) ) ) & 
% 0.21/0.49             ( ~( ( ~( m1_orders_2 @ B @ A @ B ) ) & 
% 0.21/0.49                  ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.49          | ~ (m1_orders_2 @ X15 @ X16 @ X15)
% 0.21/0.49          | ((X15) = (k1_xboole_0))
% 0.21/0.49          | ~ (l1_orders_2 @ X16)
% 0.21/0.49          | ~ (v5_orders_2 @ X16)
% 0.21/0.49          | ~ (v4_orders_2 @ X16)
% 0.21/0.49          | ~ (v3_orders_2 @ X16)
% 0.21/0.49          | (v2_struct_0 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t68_orders_2])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v3_orders_2 @ sk_A)
% 0.21/0.49        | ~ (v4_orders_2 @ sk_A)
% 0.21/0.49        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.49        | ~ (l1_orders_2 @ sk_A)
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.21/0.49  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_C) | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.49      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0)))
% 0.21/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.21/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '45'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.21/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf(d16_orders_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( v6_orders_2 @ C @ A ) & 
% 0.21/0.49                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.49               ( ( m2_orders_2 @ C @ A @ B ) <=>
% 0.21/0.49                 ( ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49                   ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C ) & 
% 0.21/0.49                   ( ![D:$i]:
% 0.21/0.49                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49                       ( ( r2_hidden @ D @ C ) =>
% 0.21/0.49                         ( ( k1_funct_1 @
% 0.21/0.49                             B @ 
% 0.21/0.49                             ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) ) =
% 0.21/0.49                           ( D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (m1_orders_1 @ X5 @ (k1_orders_1 @ (u1_struct_0 @ X6)))
% 0.21/0.49          | ~ (m2_orders_2 @ X7 @ X6 @ X5)
% 0.21/0.49          | ((X7) != (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.49          | ~ (v6_orders_2 @ X7 @ X6)
% 0.21/0.49          | ~ (l1_orders_2 @ X6)
% 0.21/0.49          | ~ (v5_orders_2 @ X6)
% 0.21/0.49          | ~ (v4_orders_2 @ X6)
% 0.21/0.49          | ~ (v3_orders_2 @ X6)
% 0.21/0.49          | (v2_struct_0 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [d16_orders_2])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X6)
% 0.21/0.49          | ~ (v3_orders_2 @ X6)
% 0.21/0.49          | ~ (v4_orders_2 @ X6)
% 0.21/0.49          | ~ (v5_orders_2 @ X6)
% 0.21/0.49          | ~ (l1_orders_2 @ X6)
% 0.21/0.49          | ~ (v6_orders_2 @ k1_xboole_0 @ X6)
% 0.21/0.49          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.49          | ~ (m2_orders_2 @ k1_xboole_0 @ X6 @ X5)
% 0.21/0.49          | ~ (m1_orders_1 @ X5 @ (k1_orders_1 @ (u1_struct_0 @ X6))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49           | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.21/0.49           | ~ (v6_orders_2 @ k1_xboole_0 @ sk_A)
% 0.21/0.49           | ~ (l1_orders_2 @ sk_A)
% 0.21/0.49           | ~ (v5_orders_2 @ sk_A)
% 0.21/0.49           | ~ (v4_orders_2 @ sk_A)
% 0.21/0.49           | ~ (v3_orders_2 @ sk_A)
% 0.21/0.49           | (v2_struct_0 @ sk_A)))
% 0.21/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.21/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['48', '50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0)))
% 0.21/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.21/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '45'])).
% 0.21/0.49  thf('53', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (l1_orders_2 @ X9)
% 0.21/0.49          | ~ (v5_orders_2 @ X9)
% 0.21/0.49          | ~ (v4_orders_2 @ X9)
% 0.21/0.49          | ~ (v3_orders_2 @ X9)
% 0.21/0.49          | (v2_struct_0 @ X9)
% 0.21/0.49          | ~ (m1_orders_1 @ X10 @ (k1_orders_1 @ (u1_struct_0 @ X9)))
% 0.21/0.49          | (v6_orders_2 @ X11 @ X9)
% 0.21/0.49          | ~ (m2_orders_2 @ X11 @ X9 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | (v6_orders_2 @ X0 @ sk_A)
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.49          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.49  thf('57', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('58', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('59', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('60', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | (v6_orders_2 @ X0 @ sk_A)
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 0.21/0.49  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v6_orders_2 @ X0 @ sk_A) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['61', '62'])).
% 0.21/0.49  thf('64', plain, ((v6_orders_2 @ sk_C @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['53', '63'])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (((v6_orders_2 @ k1_xboole_0 @ sk_A))
% 0.21/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.21/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['52', '64'])).
% 0.21/0.49  thf('66', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('67', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('68', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('69', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49           | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.21/0.49           | (v2_struct_0 @ sk_A)))
% 0.21/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.21/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['51', '65', '66', '67', '68', '69'])).
% 0.21/0.49  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('72', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.21/0.49           | ~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.21/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('clc', [status(thm)], ['70', '71'])).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      ((~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.21/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.21/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '72'])).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0)))
% 0.21/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.21/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '45'])).
% 0.21/0.49  thf('75', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('76', plain,
% 0.21/0.49      (((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.21/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.21/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['74', '75'])).
% 0.21/0.49  thf('77', plain,
% 0.21/0.49      (((r2_xboole_0 @ sk_C @ sk_D_1)) | 
% 0.21/0.49       ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['73', '76'])).
% 0.21/0.49  thf('78', plain,
% 0.21/0.49      (((r2_xboole_0 @ sk_C @ sk_D_1)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('79', plain, (((r2_xboole_0 @ sk_C @ sk_D_1))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['3', '77', '78'])).
% 0.21/0.49  thf('80', plain, ((r2_xboole_0 @ sk_C @ sk_D_1)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['1', '79'])).
% 0.21/0.49  thf('81', plain, ((m2_orders_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('82', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('83', plain,
% 0.21/0.49      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t83_orders_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.21/0.49                   ( ( ( C ) != ( D ) ) =>
% 0.21/0.49                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.21/0.49                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('84', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.49         (~ (m1_orders_1 @ X17 @ (k1_orders_1 @ (u1_struct_0 @ X18)))
% 0.21/0.49          | ~ (m2_orders_2 @ X19 @ X18 @ X17)
% 0.21/0.49          | (m1_orders_2 @ X19 @ X18 @ X20)
% 0.21/0.49          | (m1_orders_2 @ X20 @ X18 @ X19)
% 0.21/0.49          | ((X20) = (X19))
% 0.21/0.49          | ~ (m2_orders_2 @ X20 @ X18 @ X17)
% 0.21/0.49          | ~ (l1_orders_2 @ X18)
% 0.21/0.49          | ~ (v5_orders_2 @ X18)
% 0.21/0.49          | ~ (v4_orders_2 @ X18)
% 0.21/0.49          | ~ (v3_orders_2 @ X18)
% 0.21/0.49          | (v2_struct_0 @ X18))),
% 0.21/0.49      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.21/0.49  thf('85', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.49          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | ((X0) = (X1))
% 0.21/0.49          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.21/0.49          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.21/0.49          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.49  thf('86', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('87', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('88', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('90', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | ((X0) = (X1))
% 0.21/0.49          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.21/0.49          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.21/0.49          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['85', '86', '87', '88', '89'])).
% 0.21/0.49  thf('91', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.21/0.49          | (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.21/0.49          | ((sk_C) = (X0))
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['82', '90'])).
% 0.21/0.49  thf('92', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ((sk_C) = (sk_D_1))
% 0.21/0.49        | (m1_orders_2 @ sk_C @ sk_A @ sk_D_1)
% 0.21/0.49        | (m1_orders_2 @ sk_D_1 @ sk_A @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['81', '91'])).
% 0.21/0.49  thf('93', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('94', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.49          | (r1_tarski @ X14 @ X12)
% 0.21/0.49          | ~ (m1_orders_2 @ X14 @ X13 @ X12)
% 0.21/0.49          | ~ (l1_orders_2 @ X13)
% 0.21/0.49          | ~ (v5_orders_2 @ X13)
% 0.21/0.49          | ~ (v4_orders_2 @ X13)
% 0.21/0.49          | ~ (v3_orders_2 @ X13)
% 0.21/0.49          | (v2_struct_0 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.21/0.49  thf('95', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.21/0.49          | (r1_tarski @ X0 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['93', '94'])).
% 0.21/0.49  thf('96', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('97', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('98', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('99', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('100', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.21/0.49          | (r1_tarski @ X0 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 0.21/0.49  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('102', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.21/0.49      inference('clc', [status(thm)], ['100', '101'])).
% 0.21/0.49  thf('103', plain,
% 0.21/0.49      (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)
% 0.21/0.49        | ((sk_C) = (sk_D_1))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | (r1_tarski @ sk_D_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['92', '102'])).
% 0.21/0.49  thf('104', plain,
% 0.21/0.49      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D_1))
% 0.21/0.49         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['2'])).
% 0.21/0.49  thf('105', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['3', '77'])).
% 0.21/0.49  thf('106', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D_1)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['104', '105'])).
% 0.21/0.49  thf('107', plain,
% 0.21/0.49      (((r1_tarski @ sk_D_1 @ sk_C)
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ((sk_C) = (sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['103', '106'])).
% 0.21/0.49  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('109', plain, ((((sk_C) = (sk_D_1)) | (r1_tarski @ sk_D_1 @ sk_C))),
% 0.21/0.49      inference('clc', [status(thm)], ['107', '108'])).
% 0.21/0.49  thf(t60_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.21/0.49  thf('110', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X3 @ X4) | ~ (r2_xboole_0 @ X4 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.21/0.49  thf('111', plain, ((((sk_C) = (sk_D_1)) | ~ (r2_xboole_0 @ sk_C @ sk_D_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['109', '110'])).
% 0.21/0.49  thf('112', plain, ((r2_xboole_0 @ sk_C @ sk_D_1)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['1', '79'])).
% 0.21/0.49  thf('113', plain, (((sk_C) = (sk_D_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['111', '112'])).
% 0.21/0.49  thf('114', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['80', '113'])).
% 0.21/0.49  thf('115', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: (((X0) != (X1)) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.49  thf('116', plain, (![X1 : $i]: ~ (r2_xboole_0 @ X1 @ X1)),
% 0.21/0.49      inference('simplify', [status(thm)], ['115'])).
% 0.21/0.49  thf('117', plain, ($false), inference('sup-', [status(thm)], ['114', '116'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
