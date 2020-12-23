%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AHkF3zutob

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:19 EST 2020

% Result     : Theorem 40.83s
% Output     : Refutation 40.83s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 434 expanded)
%              Number of leaves         :   23 ( 135 expanded)
%              Depth                    :   26
%              Number of atoms          :  813 (4306 expanded)
%              Number of equality atoms :   19 ( 125 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t51_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ~ ( r2_hidden @ D @ C ) ) )
           => ( B
              = ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ B )
                  <=> ~ ( r2_hidden @ D @ C ) ) )
             => ( B
                = ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_xboole_0 @ X42 @ X40 )
      | ( r1_tarski @ X42 @ ( k3_subset_1 @ X41 @ X40 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_C_5 )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X45: $i] :
      ( ~ ( r2_hidden @ X45 @ sk_B )
      | ~ ( r2_hidden @ X45 @ sk_C_5 )
      | ~ ( m1_subset_1 @ X45 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r1_tarski @ X16 @ X14 )
      | ( X15
       != ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('14',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ( X15
       != ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['15','22'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','25'])).

thf('27',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( m1_subset_1 @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ( m1_subset_1 @ X26 @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ sk_C_5 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['8','30'])).

thf('32',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_5 )
    | ( r1_xboole_0 @ sk_B @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['5','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_B @ sk_C_5 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ),
    inference(demod,[status(thm)],['4','33'])).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('36',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X26: $i,X27: $i] :
      ( ( m1_subset_1 @ X26 @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('39',plain,(
    ! [X43: $i,X44: $i] :
      ( ( m1_subset_1 @ ( sk_C_4 @ X43 @ X44 ) @ X44 )
      | ( X44 = X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('40',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_C_5 )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C_4 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    sk_B
 != ( k3_subset_1 @ sk_A @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( sk_C_4 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) )
    | ( r2_hidden @ ( sk_C_4 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ),
    inference(demod,[status(thm)],['4','33'])).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_B
      = ( k3_subset_1 @ sk_A @ sk_C_5 ) )
    | ~ ( v1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    sk_B
 != ( k3_subset_1 @ sk_A @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

thf('54',plain,(
    r2_hidden @ ( sk_C_4 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ),
    inference(clc,[status(thm)],['44','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('56',plain,(
    ! [X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('57',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C_5 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_5 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('63',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_5 ) @ sk_A ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r2_hidden @ ( sk_C_4 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['54','65'])).

thf('67',plain,(
    ! [X26: $i,X27: $i] :
      ( ( m1_subset_1 @ X26 @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('68',plain,(
    m1_subset_1 @ ( sk_C_4 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X45: $i] :
      ( ( r2_hidden @ X45 @ sk_C_5 )
      | ( r2_hidden @ X45 @ sk_B )
      | ~ ( m1_subset_1 @ X45 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r2_hidden @ ( sk_C_4 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) @ sk_B )
    | ( r2_hidden @ ( sk_C_4 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r2_hidden @ ( sk_C_4 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ),
    inference(clc,[status(thm)],['44','53'])).

thf('72',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C_4 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r2_hidden @ ( sk_C_4 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) @ sk_B )
    | ~ ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('76',plain,(
    m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X42 @ ( k3_subset_1 @ X41 @ X40 ) )
      | ( r1_xboole_0 @ X42 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ sk_C_5 )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) @ sk_C_5 )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('81',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) @ sk_C_5 ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    r2_hidden @ ( sk_C_4 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) @ sk_B ),
    inference(demod,[status(thm)],['74','81'])).

thf('83',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ ( sk_C_4 @ X43 @ X44 ) @ X43 )
      | ( X44 = X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('84',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) )
    | ( ( k3_subset_1 @ sk_A @ sk_C_5 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('86',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_5 )
    = sk_B ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    sk_B
 != ( k3_subset_1 @ sk_A @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AHkF3zutob
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:42:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 40.83/41.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 40.83/41.05  % Solved by: fo/fo7.sh
% 40.83/41.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 40.83/41.05  % done 44271 iterations in 40.577s
% 40.83/41.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 40.83/41.05  % SZS output start Refutation
% 40.83/41.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 40.83/41.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 40.83/41.05  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 40.83/41.05  thf(sk_C_5_type, type, sk_C_5: $i).
% 40.83/41.05  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 40.83/41.05  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 40.83/41.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 40.83/41.05  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 40.83/41.05  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 40.83/41.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 40.83/41.05  thf(sk_A_type, type, sk_A: $i).
% 40.83/41.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 40.83/41.05  thf(sk_B_type, type, sk_B: $i).
% 40.83/41.05  thf(t51_subset_1, conjecture,
% 40.83/41.05    (![A:$i,B:$i]:
% 40.83/41.05     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 40.83/41.05       ( ![C:$i]:
% 40.83/41.05         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 40.83/41.05           ( ( ![D:$i]:
% 40.83/41.05               ( ( m1_subset_1 @ D @ A ) =>
% 40.83/41.05                 ( ( r2_hidden @ D @ B ) <=> ( ~( r2_hidden @ D @ C ) ) ) ) ) =>
% 40.83/41.05             ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 40.83/41.05  thf(zf_stmt_0, negated_conjecture,
% 40.83/41.05    (~( ![A:$i,B:$i]:
% 40.83/41.05        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 40.83/41.05          ( ![C:$i]:
% 40.83/41.05            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 40.83/41.05              ( ( ![D:$i]:
% 40.83/41.05                  ( ( m1_subset_1 @ D @ A ) =>
% 40.83/41.05                    ( ( r2_hidden @ D @ B ) <=> ( ~( r2_hidden @ D @ C ) ) ) ) ) =>
% 40.83/41.05                ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 40.83/41.05    inference('cnf.neg', [status(esa)], [t51_subset_1])).
% 40.83/41.05  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 40.83/41.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.83/41.05  thf('1', plain, ((m1_subset_1 @ sk_C_5 @ (k1_zfmisc_1 @ sk_A))),
% 40.83/41.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.83/41.05  thf(t43_subset_1, axiom,
% 40.83/41.05    (![A:$i,B:$i]:
% 40.83/41.05     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 40.83/41.05       ( ![C:$i]:
% 40.83/41.05         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 40.83/41.05           ( ( r1_xboole_0 @ B @ C ) <=>
% 40.83/41.05             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 40.83/41.05  thf('2', plain,
% 40.83/41.05      (![X40 : $i, X41 : $i, X42 : $i]:
% 40.83/41.05         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 40.83/41.05          | ~ (r1_xboole_0 @ X42 @ X40)
% 40.83/41.05          | (r1_tarski @ X42 @ (k3_subset_1 @ X41 @ X40))
% 40.83/41.05          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 40.83/41.05      inference('cnf', [status(esa)], [t43_subset_1])).
% 40.83/41.05  thf('3', plain,
% 40.83/41.05      (![X0 : $i]:
% 40.83/41.05         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 40.83/41.05          | (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_5))
% 40.83/41.05          | ~ (r1_xboole_0 @ X0 @ sk_C_5))),
% 40.83/41.05      inference('sup-', [status(thm)], ['1', '2'])).
% 40.83/41.05  thf('4', plain,
% 40.83/41.05      ((~ (r1_xboole_0 @ sk_B @ sk_C_5)
% 40.83/41.05        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 40.83/41.05      inference('sup-', [status(thm)], ['0', '3'])).
% 40.83/41.05  thf(t3_xboole_0, axiom,
% 40.83/41.05    (![A:$i,B:$i]:
% 40.83/41.05     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 40.83/41.05            ( r1_xboole_0 @ A @ B ) ) ) & 
% 40.83/41.05       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 40.83/41.05            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 40.83/41.05  thf('5', plain,
% 40.83/41.05      (![X4 : $i, X5 : $i]:
% 40.83/41.05         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 40.83/41.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 40.83/41.05  thf('6', plain,
% 40.83/41.05      (![X4 : $i, X5 : $i]:
% 40.83/41.05         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 40.83/41.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 40.83/41.05  thf('7', plain,
% 40.83/41.05      (![X45 : $i]:
% 40.83/41.05         (~ (r2_hidden @ X45 @ sk_B)
% 40.83/41.05          | ~ (r2_hidden @ X45 @ sk_C_5)
% 40.83/41.05          | ~ (m1_subset_1 @ X45 @ sk_A))),
% 40.83/41.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.83/41.05  thf('8', plain,
% 40.83/41.05      (![X0 : $i]:
% 40.83/41.05         ((r1_xboole_0 @ sk_B @ X0)
% 40.83/41.05          | ~ (m1_subset_1 @ (sk_C_1 @ X0 @ sk_B) @ sk_A)
% 40.83/41.05          | ~ (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ sk_C_5))),
% 40.83/41.05      inference('sup-', [status(thm)], ['6', '7'])).
% 40.83/41.05  thf('9', plain,
% 40.83/41.05      (![X4 : $i, X5 : $i]:
% 40.83/41.05         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 40.83/41.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 40.83/41.05  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 40.83/41.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.83/41.05  thf(d2_subset_1, axiom,
% 40.83/41.05    (![A:$i,B:$i]:
% 40.83/41.05     ( ( ( v1_xboole_0 @ A ) =>
% 40.83/41.05         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 40.83/41.05       ( ( ~( v1_xboole_0 @ A ) ) =>
% 40.83/41.05         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 40.83/41.05  thf('11', plain,
% 40.83/41.05      (![X26 : $i, X27 : $i]:
% 40.83/41.05         (~ (m1_subset_1 @ X26 @ X27)
% 40.83/41.05          | (r2_hidden @ X26 @ X27)
% 40.83/41.05          | (v1_xboole_0 @ X27))),
% 40.83/41.05      inference('cnf', [status(esa)], [d2_subset_1])).
% 40.83/41.05  thf('12', plain,
% 40.83/41.05      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 40.83/41.05        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 40.83/41.05      inference('sup-', [status(thm)], ['10', '11'])).
% 40.83/41.05  thf(d1_zfmisc_1, axiom,
% 40.83/41.05    (![A:$i,B:$i]:
% 40.83/41.05     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 40.83/41.05       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 40.83/41.05  thf('13', plain,
% 40.83/41.05      (![X14 : $i, X15 : $i, X16 : $i]:
% 40.83/41.05         (~ (r2_hidden @ X16 @ X15)
% 40.83/41.05          | (r1_tarski @ X16 @ X14)
% 40.83/41.05          | ((X15) != (k1_zfmisc_1 @ X14)))),
% 40.83/41.05      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 40.83/41.05  thf('14', plain,
% 40.83/41.05      (![X14 : $i, X16 : $i]:
% 40.83/41.05         ((r1_tarski @ X16 @ X14) | ~ (r2_hidden @ X16 @ (k1_zfmisc_1 @ X14)))),
% 40.83/41.05      inference('simplify', [status(thm)], ['13'])).
% 40.83/41.05  thf('15', plain,
% 40.83/41.05      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_B @ sk_A))),
% 40.83/41.05      inference('sup-', [status(thm)], ['12', '14'])).
% 40.83/41.05  thf(d10_xboole_0, axiom,
% 40.83/41.05    (![A:$i,B:$i]:
% 40.83/41.05     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 40.83/41.05  thf('16', plain,
% 40.83/41.05      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 40.83/41.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 40.83/41.05  thf('17', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 40.83/41.05      inference('simplify', [status(thm)], ['16'])).
% 40.83/41.05  thf('18', plain,
% 40.83/41.05      (![X13 : $i, X14 : $i, X15 : $i]:
% 40.83/41.05         (~ (r1_tarski @ X13 @ X14)
% 40.83/41.05          | (r2_hidden @ X13 @ X15)
% 40.83/41.05          | ((X15) != (k1_zfmisc_1 @ X14)))),
% 40.83/41.05      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 40.83/41.05  thf('19', plain,
% 40.83/41.05      (![X13 : $i, X14 : $i]:
% 40.83/41.05         ((r2_hidden @ X13 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X13 @ X14))),
% 40.83/41.05      inference('simplify', [status(thm)], ['18'])).
% 40.83/41.05  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 40.83/41.05      inference('sup-', [status(thm)], ['17', '19'])).
% 40.83/41.05  thf(t7_boole, axiom,
% 40.83/41.05    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 40.83/41.05  thf('21', plain,
% 40.83/41.05      (![X11 : $i, X12 : $i]:
% 40.83/41.05         (~ (r2_hidden @ X11 @ X12) | ~ (v1_xboole_0 @ X12))),
% 40.83/41.05      inference('cnf', [status(esa)], [t7_boole])).
% 40.83/41.05  thf('22', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 40.83/41.05      inference('sup-', [status(thm)], ['20', '21'])).
% 40.83/41.05  thf('23', plain, ((r1_tarski @ sk_B @ sk_A)),
% 40.83/41.05      inference('clc', [status(thm)], ['15', '22'])).
% 40.83/41.05  thf(d3_tarski, axiom,
% 40.83/41.05    (![A:$i,B:$i]:
% 40.83/41.05     ( ( r1_tarski @ A @ B ) <=>
% 40.83/41.05       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 40.83/41.05  thf('24', plain,
% 40.83/41.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.83/41.05         (~ (r2_hidden @ X0 @ X1)
% 40.83/41.05          | (r2_hidden @ X0 @ X2)
% 40.83/41.05          | ~ (r1_tarski @ X1 @ X2))),
% 40.83/41.05      inference('cnf', [status(esa)], [d3_tarski])).
% 40.83/41.05  thf('25', plain,
% 40.83/41.05      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 40.83/41.05      inference('sup-', [status(thm)], ['23', '24'])).
% 40.83/41.05  thf('26', plain,
% 40.83/41.05      (![X0 : $i]:
% 40.83/41.05         ((r1_xboole_0 @ sk_B @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ sk_A))),
% 40.83/41.05      inference('sup-', [status(thm)], ['9', '25'])).
% 40.83/41.05  thf('27', plain,
% 40.83/41.05      (![X26 : $i, X27 : $i]:
% 40.83/41.05         (~ (r2_hidden @ X26 @ X27)
% 40.83/41.05          | (m1_subset_1 @ X26 @ X27)
% 40.83/41.05          | (v1_xboole_0 @ X27))),
% 40.83/41.05      inference('cnf', [status(esa)], [d2_subset_1])).
% 40.83/41.05  thf('28', plain,
% 40.83/41.05      (![X11 : $i, X12 : $i]:
% 40.83/41.05         (~ (r2_hidden @ X11 @ X12) | ~ (v1_xboole_0 @ X12))),
% 40.83/41.05      inference('cnf', [status(esa)], [t7_boole])).
% 40.83/41.05  thf('29', plain,
% 40.83/41.05      (![X26 : $i, X27 : $i]:
% 40.83/41.05         ((m1_subset_1 @ X26 @ X27) | ~ (r2_hidden @ X26 @ X27))),
% 40.83/41.05      inference('clc', [status(thm)], ['27', '28'])).
% 40.83/41.05  thf('30', plain,
% 40.83/41.05      (![X0 : $i]:
% 40.83/41.05         ((r1_xboole_0 @ sk_B @ X0)
% 40.83/41.05          | (m1_subset_1 @ (sk_C_1 @ X0 @ sk_B) @ sk_A))),
% 40.83/41.05      inference('sup-', [status(thm)], ['26', '29'])).
% 40.83/41.05  thf('31', plain,
% 40.83/41.05      (![X0 : $i]:
% 40.83/41.05         (~ (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ sk_C_5)
% 40.83/41.05          | (r1_xboole_0 @ sk_B @ X0))),
% 40.83/41.05      inference('clc', [status(thm)], ['8', '30'])).
% 40.83/41.05  thf('32', plain,
% 40.83/41.05      (((r1_xboole_0 @ sk_B @ sk_C_5) | (r1_xboole_0 @ sk_B @ sk_C_5))),
% 40.83/41.05      inference('sup-', [status(thm)], ['5', '31'])).
% 40.83/41.05  thf('33', plain, ((r1_xboole_0 @ sk_B @ sk_C_5)),
% 40.83/41.05      inference('simplify', [status(thm)], ['32'])).
% 40.83/41.05  thf('34', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5))),
% 40.83/41.05      inference('demod', [status(thm)], ['4', '33'])).
% 40.83/41.05  thf('35', plain,
% 40.83/41.05      (![X13 : $i, X14 : $i]:
% 40.83/41.05         ((r2_hidden @ X13 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X13 @ X14))),
% 40.83/41.05      inference('simplify', [status(thm)], ['18'])).
% 40.83/41.05  thf('36', plain,
% 40.83/41.05      ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 40.83/41.05      inference('sup-', [status(thm)], ['34', '35'])).
% 40.83/41.05  thf('37', plain,
% 40.83/41.05      (![X26 : $i, X27 : $i]:
% 40.83/41.05         ((m1_subset_1 @ X26 @ X27) | ~ (r2_hidden @ X26 @ X27))),
% 40.83/41.05      inference('clc', [status(thm)], ['27', '28'])).
% 40.83/41.05  thf('38', plain,
% 40.83/41.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 40.83/41.05      inference('sup-', [status(thm)], ['36', '37'])).
% 40.83/41.05  thf(t49_subset_1, axiom,
% 40.83/41.05    (![A:$i,B:$i]:
% 40.83/41.05     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 40.83/41.05       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 40.83/41.05         ( ( A ) = ( B ) ) ) ))).
% 40.83/41.05  thf('39', plain,
% 40.83/41.05      (![X43 : $i, X44 : $i]:
% 40.83/41.05         ((m1_subset_1 @ (sk_C_4 @ X43 @ X44) @ X44)
% 40.83/41.05          | ((X44) = (X43))
% 40.83/41.05          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 40.83/41.05      inference('cnf', [status(esa)], [t49_subset_1])).
% 40.83/41.05  thf('40', plain,
% 40.83/41.05      ((((k3_subset_1 @ sk_A @ sk_C_5) = (sk_B))
% 40.83/41.05        | (m1_subset_1 @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ 
% 40.83/41.05           (k3_subset_1 @ sk_A @ sk_C_5)))),
% 40.83/41.05      inference('sup-', [status(thm)], ['38', '39'])).
% 40.83/41.05  thf('41', plain, (((sk_B) != (k3_subset_1 @ sk_A @ sk_C_5))),
% 40.83/41.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.83/41.05  thf('42', plain,
% 40.83/41.05      ((m1_subset_1 @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ 
% 40.83/41.05        (k3_subset_1 @ sk_A @ sk_C_5))),
% 40.83/41.05      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 40.83/41.05  thf('43', plain,
% 40.83/41.05      (![X26 : $i, X27 : $i]:
% 40.83/41.05         (~ (m1_subset_1 @ X26 @ X27)
% 40.83/41.05          | (r2_hidden @ X26 @ X27)
% 40.83/41.05          | (v1_xboole_0 @ X27))),
% 40.83/41.05      inference('cnf', [status(esa)], [d2_subset_1])).
% 40.83/41.05  thf('44', plain,
% 40.83/41.05      (((v1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_5))
% 40.83/41.05        | (r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ 
% 40.83/41.05           (k3_subset_1 @ sk_A @ sk_C_5)))),
% 40.83/41.05      inference('sup-', [status(thm)], ['42', '43'])).
% 40.83/41.05  thf('45', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5))),
% 40.83/41.05      inference('demod', [status(thm)], ['4', '33'])).
% 40.83/41.05  thf('46', plain,
% 40.83/41.05      (![X1 : $i, X3 : $i]:
% 40.83/41.05         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 40.83/41.05      inference('cnf', [status(esa)], [d3_tarski])).
% 40.83/41.05  thf('47', plain,
% 40.83/41.05      (![X11 : $i, X12 : $i]:
% 40.83/41.05         (~ (r2_hidden @ X11 @ X12) | ~ (v1_xboole_0 @ X12))),
% 40.83/41.05      inference('cnf', [status(esa)], [t7_boole])).
% 40.83/41.05  thf('48', plain,
% 40.83/41.05      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 40.83/41.05      inference('sup-', [status(thm)], ['46', '47'])).
% 40.83/41.05  thf('49', plain,
% 40.83/41.05      (![X8 : $i, X10 : $i]:
% 40.83/41.05         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 40.83/41.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 40.83/41.05  thf('50', plain,
% 40.83/41.05      (![X0 : $i, X1 : $i]:
% 40.83/41.05         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 40.83/41.05      inference('sup-', [status(thm)], ['48', '49'])).
% 40.83/41.05  thf('51', plain,
% 40.83/41.05      ((((sk_B) = (k3_subset_1 @ sk_A @ sk_C_5))
% 40.83/41.05        | ~ (v1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 40.83/41.05      inference('sup-', [status(thm)], ['45', '50'])).
% 40.83/41.05  thf('52', plain, (((sk_B) != (k3_subset_1 @ sk_A @ sk_C_5))),
% 40.83/41.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.83/41.05  thf('53', plain, (~ (v1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_5))),
% 40.83/41.05      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 40.83/41.05  thf('54', plain,
% 40.83/41.05      ((r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ 
% 40.83/41.05        (k3_subset_1 @ sk_A @ sk_C_5))),
% 40.83/41.05      inference('clc', [status(thm)], ['44', '53'])).
% 40.83/41.05  thf('55', plain, ((m1_subset_1 @ sk_C_5 @ (k1_zfmisc_1 @ sk_A))),
% 40.83/41.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.83/41.05  thf(dt_k3_subset_1, axiom,
% 40.83/41.05    (![A:$i,B:$i]:
% 40.83/41.05     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 40.83/41.05       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 40.83/41.05  thf('56', plain,
% 40.83/41.05      (![X32 : $i, X33 : $i]:
% 40.83/41.05         ((m1_subset_1 @ (k3_subset_1 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))
% 40.83/41.05          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 40.83/41.05      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 40.83/41.05  thf('57', plain,
% 40.83/41.05      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_5) @ (k1_zfmisc_1 @ sk_A))),
% 40.83/41.05      inference('sup-', [status(thm)], ['55', '56'])).
% 40.83/41.05  thf('58', plain,
% 40.83/41.05      (![X26 : $i, X27 : $i]:
% 40.83/41.05         (~ (m1_subset_1 @ X26 @ X27)
% 40.83/41.05          | (r2_hidden @ X26 @ X27)
% 40.83/41.05          | (v1_xboole_0 @ X27))),
% 40.83/41.05      inference('cnf', [status(esa)], [d2_subset_1])).
% 40.83/41.05  thf('59', plain,
% 40.83/41.06      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 40.83/41.06        | (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C_5) @ (k1_zfmisc_1 @ sk_A)))),
% 40.83/41.06      inference('sup-', [status(thm)], ['57', '58'])).
% 40.83/41.06  thf('60', plain,
% 40.83/41.06      (![X14 : $i, X16 : $i]:
% 40.83/41.06         ((r1_tarski @ X16 @ X14) | ~ (r2_hidden @ X16 @ (k1_zfmisc_1 @ X14)))),
% 40.83/41.06      inference('simplify', [status(thm)], ['13'])).
% 40.83/41.06  thf('61', plain,
% 40.83/41.06      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 40.83/41.06        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_5) @ sk_A))),
% 40.83/41.06      inference('sup-', [status(thm)], ['59', '60'])).
% 40.83/41.06  thf('62', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 40.83/41.06      inference('sup-', [status(thm)], ['20', '21'])).
% 40.83/41.06  thf('63', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_5) @ sk_A)),
% 40.83/41.06      inference('clc', [status(thm)], ['61', '62'])).
% 40.83/41.06  thf('64', plain,
% 40.83/41.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.83/41.06         (~ (r2_hidden @ X0 @ X1)
% 40.83/41.06          | (r2_hidden @ X0 @ X2)
% 40.83/41.06          | ~ (r1_tarski @ X1 @ X2))),
% 40.83/41.06      inference('cnf', [status(esa)], [d3_tarski])).
% 40.83/41.06  thf('65', plain,
% 40.83/41.06      (![X0 : $i]:
% 40.83/41.06         ((r2_hidden @ X0 @ sk_A)
% 40.83/41.06          | ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 40.83/41.06      inference('sup-', [status(thm)], ['63', '64'])).
% 40.83/41.06  thf('66', plain,
% 40.83/41.06      ((r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ sk_A)),
% 40.83/41.06      inference('sup-', [status(thm)], ['54', '65'])).
% 40.83/41.06  thf('67', plain,
% 40.83/41.06      (![X26 : $i, X27 : $i]:
% 40.83/41.06         ((m1_subset_1 @ X26 @ X27) | ~ (r2_hidden @ X26 @ X27))),
% 40.83/41.06      inference('clc', [status(thm)], ['27', '28'])).
% 40.83/41.06  thf('68', plain,
% 40.83/41.06      ((m1_subset_1 @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ sk_A)),
% 40.83/41.06      inference('sup-', [status(thm)], ['66', '67'])).
% 40.83/41.06  thf('69', plain,
% 40.83/41.06      (![X45 : $i]:
% 40.83/41.06         ((r2_hidden @ X45 @ sk_C_5)
% 40.83/41.06          | (r2_hidden @ X45 @ sk_B)
% 40.83/41.06          | ~ (m1_subset_1 @ X45 @ sk_A))),
% 40.83/41.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.83/41.06  thf('70', plain,
% 40.83/41.06      (((r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ sk_B)
% 40.83/41.06        | (r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ sk_C_5))),
% 40.83/41.06      inference('sup-', [status(thm)], ['68', '69'])).
% 40.83/41.06  thf('71', plain,
% 40.83/41.06      ((r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ 
% 40.83/41.06        (k3_subset_1 @ sk_A @ sk_C_5))),
% 40.83/41.06      inference('clc', [status(thm)], ['44', '53'])).
% 40.83/41.06  thf('72', plain,
% 40.83/41.06      (![X4 : $i, X6 : $i, X7 : $i]:
% 40.83/41.06         (~ (r2_hidden @ X6 @ X4)
% 40.83/41.06          | ~ (r2_hidden @ X6 @ X7)
% 40.83/41.06          | ~ (r1_xboole_0 @ X4 @ X7))),
% 40.83/41.06      inference('cnf', [status(esa)], [t3_xboole_0])).
% 40.83/41.06  thf('73', plain,
% 40.83/41.06      (![X0 : $i]:
% 40.83/41.06         (~ (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_5) @ X0)
% 40.83/41.06          | ~ (r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ X0))),
% 40.83/41.06      inference('sup-', [status(thm)], ['71', '72'])).
% 40.83/41.06  thf('74', plain,
% 40.83/41.06      (((r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ sk_B)
% 40.83/41.06        | ~ (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_5) @ sk_C_5))),
% 40.83/41.06      inference('sup-', [status(thm)], ['70', '73'])).
% 40.83/41.06  thf('75', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 40.83/41.06      inference('simplify', [status(thm)], ['16'])).
% 40.83/41.06  thf('76', plain, ((m1_subset_1 @ sk_C_5 @ (k1_zfmisc_1 @ sk_A))),
% 40.83/41.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.83/41.06  thf('77', plain,
% 40.83/41.06      (![X40 : $i, X41 : $i, X42 : $i]:
% 40.83/41.06         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 40.83/41.06          | ~ (r1_tarski @ X42 @ (k3_subset_1 @ X41 @ X40))
% 40.83/41.06          | (r1_xboole_0 @ X42 @ X40)
% 40.83/41.06          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 40.83/41.06      inference('cnf', [status(esa)], [t43_subset_1])).
% 40.83/41.06  thf('78', plain,
% 40.83/41.06      (![X0 : $i]:
% 40.83/41.06         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 40.83/41.06          | (r1_xboole_0 @ X0 @ sk_C_5)
% 40.83/41.06          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 40.83/41.06      inference('sup-', [status(thm)], ['76', '77'])).
% 40.83/41.06  thf('79', plain,
% 40.83/41.06      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_5) @ sk_C_5)
% 40.83/41.06        | ~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_5) @ (k1_zfmisc_1 @ sk_A)))),
% 40.83/41.06      inference('sup-', [status(thm)], ['75', '78'])).
% 40.83/41.06  thf('80', plain,
% 40.83/41.06      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_5) @ (k1_zfmisc_1 @ sk_A))),
% 40.83/41.06      inference('sup-', [status(thm)], ['55', '56'])).
% 40.83/41.06  thf('81', plain, ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_5) @ sk_C_5)),
% 40.83/41.06      inference('demod', [status(thm)], ['79', '80'])).
% 40.83/41.06  thf('82', plain,
% 40.83/41.06      ((r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ sk_B)),
% 40.83/41.06      inference('demod', [status(thm)], ['74', '81'])).
% 40.83/41.06  thf('83', plain,
% 40.83/41.06      (![X43 : $i, X44 : $i]:
% 40.83/41.06         (~ (r2_hidden @ (sk_C_4 @ X43 @ X44) @ X43)
% 40.83/41.06          | ((X44) = (X43))
% 40.83/41.06          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 40.83/41.06      inference('cnf', [status(esa)], [t49_subset_1])).
% 40.83/41.06  thf('84', plain,
% 40.83/41.06      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_A @ sk_C_5)))
% 40.83/41.06        | ((k3_subset_1 @ sk_A @ sk_C_5) = (sk_B)))),
% 40.83/41.06      inference('sup-', [status(thm)], ['82', '83'])).
% 40.83/41.06  thf('85', plain,
% 40.83/41.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 40.83/41.06      inference('sup-', [status(thm)], ['36', '37'])).
% 40.83/41.06  thf('86', plain, (((k3_subset_1 @ sk_A @ sk_C_5) = (sk_B))),
% 40.83/41.06      inference('demod', [status(thm)], ['84', '85'])).
% 40.83/41.06  thf('87', plain, (((sk_B) != (k3_subset_1 @ sk_A @ sk_C_5))),
% 40.83/41.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.83/41.06  thf('88', plain, ($false),
% 40.83/41.06      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 40.83/41.06  
% 40.83/41.06  % SZS output end Refutation
% 40.83/41.06  
% 40.83/41.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
