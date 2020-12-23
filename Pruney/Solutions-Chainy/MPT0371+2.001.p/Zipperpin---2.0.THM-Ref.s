%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QXwzrSykVo

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:19 EST 2020

% Result     : Theorem 42.50s
% Output     : Refutation 42.50s
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

thf(t52_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ~ ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B
              = ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ~ ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B
                = ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_subset_1])).

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
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X45: $i] :
      ( ~ ( r2_hidden @ X45 @ sk_C_5 )
      | ~ ( r2_hidden @ X45 @ sk_B )
      | ~ ( m1_subset_1 @ X45 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_5 )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ sk_C_5 @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ ( sk_C_1 @ sk_C_5 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ sk_A ) ),
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
    | ( r2_hidden @ sk_C_5 @ ( k1_zfmisc_1 @ sk_A ) ) ),
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
    | ( r1_tarski @ sk_C_5 @ sk_A ) ),
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
    r1_tarski @ sk_C_5 @ sk_A ),
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
      | ~ ( r2_hidden @ X0 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_5 )
      | ( r2_hidden @ ( sk_C_1 @ sk_C_5 @ X0 ) @ sk_A ) ) ),
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
      ( ( r1_xboole_0 @ X0 @ sk_C_5 )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_C_5 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ sk_C_5 @ X0 ) @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_C_5 ) ) ),
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
      ( ( r2_hidden @ X45 @ sk_B )
      | ( r2_hidden @ X45 @ sk_C_5 )
      | ~ ( m1_subset_1 @ X45 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r2_hidden @ ( sk_C_4 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) @ sk_C_5 )
    | ( r2_hidden @ ( sk_C_4 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) @ sk_B ) ),
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
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QXwzrSykVo
% 0.14/0.36  % Computer   : n025.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 09:57:50 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 42.50/42.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 42.50/42.71  % Solved by: fo/fo7.sh
% 42.50/42.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 42.50/42.71  % done 44254 iterations in 42.230s
% 42.50/42.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 42.50/42.71  % SZS output start Refutation
% 42.50/42.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 42.50/42.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 42.50/42.71  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 42.50/42.71  thf(sk_C_5_type, type, sk_C_5: $i).
% 42.50/42.71  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 42.50/42.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 42.50/42.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 42.50/42.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 42.50/42.71  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 42.50/42.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 42.50/42.71  thf(sk_A_type, type, sk_A: $i).
% 42.50/42.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 42.50/42.71  thf(sk_B_type, type, sk_B: $i).
% 42.50/42.71  thf(t52_subset_1, conjecture,
% 42.50/42.71    (![A:$i,B:$i]:
% 42.50/42.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 42.50/42.71       ( ![C:$i]:
% 42.50/42.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 42.50/42.71           ( ( ![D:$i]:
% 42.50/42.71               ( ( m1_subset_1 @ D @ A ) =>
% 42.50/42.71                 ( ( ~( r2_hidden @ D @ B ) ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 42.50/42.71             ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 42.50/42.71  thf(zf_stmt_0, negated_conjecture,
% 42.50/42.71    (~( ![A:$i,B:$i]:
% 42.50/42.71        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 42.50/42.71          ( ![C:$i]:
% 42.50/42.71            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 42.50/42.71              ( ( ![D:$i]:
% 42.50/42.71                  ( ( m1_subset_1 @ D @ A ) =>
% 42.50/42.71                    ( ( ~( r2_hidden @ D @ B ) ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 42.50/42.71                ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 42.50/42.71    inference('cnf.neg', [status(esa)], [t52_subset_1])).
% 42.50/42.71  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 42.50/42.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.50/42.71  thf('1', plain, ((m1_subset_1 @ sk_C_5 @ (k1_zfmisc_1 @ sk_A))),
% 42.50/42.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.50/42.71  thf(t43_subset_1, axiom,
% 42.50/42.71    (![A:$i,B:$i]:
% 42.50/42.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 42.50/42.71       ( ![C:$i]:
% 42.50/42.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 42.50/42.71           ( ( r1_xboole_0 @ B @ C ) <=>
% 42.50/42.71             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 42.50/42.71  thf('2', plain,
% 42.50/42.71      (![X40 : $i, X41 : $i, X42 : $i]:
% 42.50/42.71         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 42.50/42.71          | ~ (r1_xboole_0 @ X42 @ X40)
% 42.50/42.71          | (r1_tarski @ X42 @ (k3_subset_1 @ X41 @ X40))
% 42.50/42.71          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 42.50/42.71      inference('cnf', [status(esa)], [t43_subset_1])).
% 42.50/42.71  thf('3', plain,
% 42.50/42.71      (![X0 : $i]:
% 42.50/42.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 42.50/42.71          | (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_5))
% 42.50/42.71          | ~ (r1_xboole_0 @ X0 @ sk_C_5))),
% 42.50/42.71      inference('sup-', [status(thm)], ['1', '2'])).
% 42.50/42.71  thf('4', plain,
% 42.50/42.71      ((~ (r1_xboole_0 @ sk_B @ sk_C_5)
% 42.50/42.71        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 42.50/42.71      inference('sup-', [status(thm)], ['0', '3'])).
% 42.50/42.71  thf(t3_xboole_0, axiom,
% 42.50/42.71    (![A:$i,B:$i]:
% 42.50/42.71     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 42.50/42.71            ( r1_xboole_0 @ A @ B ) ) ) & 
% 42.50/42.71       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 42.50/42.71            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 42.50/42.71  thf('5', plain,
% 42.50/42.71      (![X4 : $i, X5 : $i]:
% 42.50/42.71         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 42.50/42.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.50/42.71  thf('6', plain,
% 42.50/42.71      (![X4 : $i, X5 : $i]:
% 42.50/42.71         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 42.50/42.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.50/42.71  thf('7', plain,
% 42.50/42.71      (![X45 : $i]:
% 42.50/42.71         (~ (r2_hidden @ X45 @ sk_C_5)
% 42.50/42.71          | ~ (r2_hidden @ X45 @ sk_B)
% 42.50/42.71          | ~ (m1_subset_1 @ X45 @ sk_A))),
% 42.50/42.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.50/42.71  thf('8', plain,
% 42.50/42.71      (![X0 : $i]:
% 42.50/42.71         ((r1_xboole_0 @ X0 @ sk_C_5)
% 42.50/42.71          | ~ (m1_subset_1 @ (sk_C_1 @ sk_C_5 @ X0) @ sk_A)
% 42.50/42.71          | ~ (r2_hidden @ (sk_C_1 @ sk_C_5 @ X0) @ sk_B))),
% 42.50/42.71      inference('sup-', [status(thm)], ['6', '7'])).
% 42.50/42.71  thf('9', plain,
% 42.50/42.71      (![X4 : $i, X5 : $i]:
% 42.50/42.71         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 42.50/42.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.50/42.71  thf('10', plain, ((m1_subset_1 @ sk_C_5 @ (k1_zfmisc_1 @ sk_A))),
% 42.50/42.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.50/42.71  thf(d2_subset_1, axiom,
% 42.50/42.71    (![A:$i,B:$i]:
% 42.50/42.71     ( ( ( v1_xboole_0 @ A ) =>
% 42.50/42.71         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 42.50/42.71       ( ( ~( v1_xboole_0 @ A ) ) =>
% 42.50/42.71         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 42.50/42.71  thf('11', plain,
% 42.50/42.71      (![X26 : $i, X27 : $i]:
% 42.50/42.71         (~ (m1_subset_1 @ X26 @ X27)
% 42.50/42.71          | (r2_hidden @ X26 @ X27)
% 42.50/42.71          | (v1_xboole_0 @ X27))),
% 42.50/42.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 42.50/42.71  thf('12', plain,
% 42.50/42.71      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 42.50/42.71        | (r2_hidden @ sk_C_5 @ (k1_zfmisc_1 @ sk_A)))),
% 42.50/42.71      inference('sup-', [status(thm)], ['10', '11'])).
% 42.50/42.71  thf(d1_zfmisc_1, axiom,
% 42.50/42.71    (![A:$i,B:$i]:
% 42.50/42.71     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 42.50/42.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 42.50/42.71  thf('13', plain,
% 42.50/42.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 42.50/42.71         (~ (r2_hidden @ X16 @ X15)
% 42.50/42.71          | (r1_tarski @ X16 @ X14)
% 42.50/42.71          | ((X15) != (k1_zfmisc_1 @ X14)))),
% 42.50/42.71      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 42.50/42.71  thf('14', plain,
% 42.50/42.71      (![X14 : $i, X16 : $i]:
% 42.50/42.71         ((r1_tarski @ X16 @ X14) | ~ (r2_hidden @ X16 @ (k1_zfmisc_1 @ X14)))),
% 42.50/42.71      inference('simplify', [status(thm)], ['13'])).
% 42.50/42.71  thf('15', plain,
% 42.50/42.71      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_C_5 @ sk_A))),
% 42.50/42.71      inference('sup-', [status(thm)], ['12', '14'])).
% 42.50/42.71  thf(d10_xboole_0, axiom,
% 42.50/42.71    (![A:$i,B:$i]:
% 42.50/42.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 42.50/42.71  thf('16', plain,
% 42.50/42.71      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 42.50/42.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 42.50/42.71  thf('17', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 42.50/42.71      inference('simplify', [status(thm)], ['16'])).
% 42.50/42.71  thf('18', plain,
% 42.50/42.71      (![X13 : $i, X14 : $i, X15 : $i]:
% 42.50/42.71         (~ (r1_tarski @ X13 @ X14)
% 42.50/42.71          | (r2_hidden @ X13 @ X15)
% 42.50/42.71          | ((X15) != (k1_zfmisc_1 @ X14)))),
% 42.50/42.71      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 42.50/42.71  thf('19', plain,
% 42.50/42.71      (![X13 : $i, X14 : $i]:
% 42.50/42.71         ((r2_hidden @ X13 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X13 @ X14))),
% 42.50/42.71      inference('simplify', [status(thm)], ['18'])).
% 42.50/42.71  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 42.50/42.71      inference('sup-', [status(thm)], ['17', '19'])).
% 42.50/42.71  thf(t7_boole, axiom,
% 42.50/42.71    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 42.50/42.71  thf('21', plain,
% 42.50/42.71      (![X11 : $i, X12 : $i]:
% 42.50/42.71         (~ (r2_hidden @ X11 @ X12) | ~ (v1_xboole_0 @ X12))),
% 42.50/42.71      inference('cnf', [status(esa)], [t7_boole])).
% 42.50/42.71  thf('22', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 42.50/42.71      inference('sup-', [status(thm)], ['20', '21'])).
% 42.50/42.71  thf('23', plain, ((r1_tarski @ sk_C_5 @ sk_A)),
% 42.50/42.71      inference('clc', [status(thm)], ['15', '22'])).
% 42.50/42.71  thf(d3_tarski, axiom,
% 42.50/42.71    (![A:$i,B:$i]:
% 42.50/42.71     ( ( r1_tarski @ A @ B ) <=>
% 42.50/42.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 42.50/42.71  thf('24', plain,
% 42.50/42.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.50/42.71         (~ (r2_hidden @ X0 @ X1)
% 42.50/42.71          | (r2_hidden @ X0 @ X2)
% 42.50/42.71          | ~ (r1_tarski @ X1 @ X2))),
% 42.50/42.71      inference('cnf', [status(esa)], [d3_tarski])).
% 42.50/42.71  thf('25', plain,
% 42.50/42.71      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_5))),
% 42.50/42.71      inference('sup-', [status(thm)], ['23', '24'])).
% 42.50/42.71  thf('26', plain,
% 42.50/42.71      (![X0 : $i]:
% 42.50/42.71         ((r1_xboole_0 @ X0 @ sk_C_5)
% 42.50/42.71          | (r2_hidden @ (sk_C_1 @ sk_C_5 @ X0) @ sk_A))),
% 42.50/42.71      inference('sup-', [status(thm)], ['9', '25'])).
% 42.50/42.71  thf('27', plain,
% 42.50/42.71      (![X26 : $i, X27 : $i]:
% 42.50/42.71         (~ (r2_hidden @ X26 @ X27)
% 42.50/42.71          | (m1_subset_1 @ X26 @ X27)
% 42.50/42.71          | (v1_xboole_0 @ X27))),
% 42.50/42.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 42.50/42.71  thf('28', plain,
% 42.50/42.71      (![X11 : $i, X12 : $i]:
% 42.50/42.71         (~ (r2_hidden @ X11 @ X12) | ~ (v1_xboole_0 @ X12))),
% 42.50/42.71      inference('cnf', [status(esa)], [t7_boole])).
% 42.50/42.71  thf('29', plain,
% 42.50/42.71      (![X26 : $i, X27 : $i]:
% 42.50/42.71         ((m1_subset_1 @ X26 @ X27) | ~ (r2_hidden @ X26 @ X27))),
% 42.50/42.71      inference('clc', [status(thm)], ['27', '28'])).
% 42.50/42.71  thf('30', plain,
% 42.50/42.71      (![X0 : $i]:
% 42.50/42.71         ((r1_xboole_0 @ X0 @ sk_C_5)
% 42.50/42.71          | (m1_subset_1 @ (sk_C_1 @ sk_C_5 @ X0) @ sk_A))),
% 42.50/42.71      inference('sup-', [status(thm)], ['26', '29'])).
% 42.50/42.71  thf('31', plain,
% 42.50/42.71      (![X0 : $i]:
% 42.50/42.71         (~ (r2_hidden @ (sk_C_1 @ sk_C_5 @ X0) @ sk_B)
% 42.50/42.71          | (r1_xboole_0 @ X0 @ sk_C_5))),
% 42.50/42.71      inference('clc', [status(thm)], ['8', '30'])).
% 42.50/42.71  thf('32', plain,
% 42.50/42.71      (((r1_xboole_0 @ sk_B @ sk_C_5) | (r1_xboole_0 @ sk_B @ sk_C_5))),
% 42.50/42.71      inference('sup-', [status(thm)], ['5', '31'])).
% 42.50/42.71  thf('33', plain, ((r1_xboole_0 @ sk_B @ sk_C_5)),
% 42.50/42.71      inference('simplify', [status(thm)], ['32'])).
% 42.50/42.71  thf('34', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5))),
% 42.50/42.71      inference('demod', [status(thm)], ['4', '33'])).
% 42.50/42.71  thf('35', plain,
% 42.50/42.71      (![X13 : $i, X14 : $i]:
% 42.50/42.71         ((r2_hidden @ X13 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X13 @ X14))),
% 42.50/42.71      inference('simplify', [status(thm)], ['18'])).
% 42.50/42.71  thf('36', plain,
% 42.50/42.71      ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 42.50/42.71      inference('sup-', [status(thm)], ['34', '35'])).
% 42.50/42.71  thf('37', plain,
% 42.50/42.71      (![X26 : $i, X27 : $i]:
% 42.50/42.71         ((m1_subset_1 @ X26 @ X27) | ~ (r2_hidden @ X26 @ X27))),
% 42.50/42.71      inference('clc', [status(thm)], ['27', '28'])).
% 42.50/42.71  thf('38', plain,
% 42.50/42.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 42.50/42.71      inference('sup-', [status(thm)], ['36', '37'])).
% 42.50/42.71  thf(t49_subset_1, axiom,
% 42.50/42.71    (![A:$i,B:$i]:
% 42.50/42.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 42.50/42.71       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 42.50/42.71         ( ( A ) = ( B ) ) ) ))).
% 42.50/42.71  thf('39', plain,
% 42.50/42.71      (![X43 : $i, X44 : $i]:
% 42.50/42.71         ((m1_subset_1 @ (sk_C_4 @ X43 @ X44) @ X44)
% 42.50/42.71          | ((X44) = (X43))
% 42.50/42.71          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 42.50/42.71      inference('cnf', [status(esa)], [t49_subset_1])).
% 42.50/42.71  thf('40', plain,
% 42.50/42.71      ((((k3_subset_1 @ sk_A @ sk_C_5) = (sk_B))
% 42.50/42.71        | (m1_subset_1 @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ 
% 42.50/42.71           (k3_subset_1 @ sk_A @ sk_C_5)))),
% 42.50/42.71      inference('sup-', [status(thm)], ['38', '39'])).
% 42.50/42.71  thf('41', plain, (((sk_B) != (k3_subset_1 @ sk_A @ sk_C_5))),
% 42.50/42.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.50/42.71  thf('42', plain,
% 42.50/42.71      ((m1_subset_1 @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ 
% 42.50/42.71        (k3_subset_1 @ sk_A @ sk_C_5))),
% 42.50/42.71      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 42.50/42.71  thf('43', plain,
% 42.50/42.71      (![X26 : $i, X27 : $i]:
% 42.50/42.71         (~ (m1_subset_1 @ X26 @ X27)
% 42.50/42.71          | (r2_hidden @ X26 @ X27)
% 42.50/42.71          | (v1_xboole_0 @ X27))),
% 42.50/42.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 42.50/42.71  thf('44', plain,
% 42.50/42.71      (((v1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_5))
% 42.50/42.71        | (r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ 
% 42.50/42.71           (k3_subset_1 @ sk_A @ sk_C_5)))),
% 42.50/42.71      inference('sup-', [status(thm)], ['42', '43'])).
% 42.50/42.71  thf('45', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5))),
% 42.50/42.71      inference('demod', [status(thm)], ['4', '33'])).
% 42.50/42.71  thf('46', plain,
% 42.50/42.71      (![X1 : $i, X3 : $i]:
% 42.50/42.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 42.50/42.71      inference('cnf', [status(esa)], [d3_tarski])).
% 42.50/42.71  thf('47', plain,
% 42.50/42.71      (![X11 : $i, X12 : $i]:
% 42.50/42.71         (~ (r2_hidden @ X11 @ X12) | ~ (v1_xboole_0 @ X12))),
% 42.50/42.71      inference('cnf', [status(esa)], [t7_boole])).
% 42.50/42.71  thf('48', plain,
% 42.50/42.71      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 42.50/42.71      inference('sup-', [status(thm)], ['46', '47'])).
% 42.50/42.71  thf('49', plain,
% 42.50/42.71      (![X8 : $i, X10 : $i]:
% 42.50/42.71         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 42.50/42.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 42.50/42.71  thf('50', plain,
% 42.50/42.71      (![X0 : $i, X1 : $i]:
% 42.50/42.71         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 42.50/42.71      inference('sup-', [status(thm)], ['48', '49'])).
% 42.50/42.71  thf('51', plain,
% 42.50/42.71      ((((sk_B) = (k3_subset_1 @ sk_A @ sk_C_5))
% 42.50/42.71        | ~ (v1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 42.50/42.71      inference('sup-', [status(thm)], ['45', '50'])).
% 42.50/42.71  thf('52', plain, (((sk_B) != (k3_subset_1 @ sk_A @ sk_C_5))),
% 42.50/42.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.50/42.71  thf('53', plain, (~ (v1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_5))),
% 42.50/42.71      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 42.50/42.71  thf('54', plain,
% 42.50/42.71      ((r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ 
% 42.50/42.71        (k3_subset_1 @ sk_A @ sk_C_5))),
% 42.50/42.71      inference('clc', [status(thm)], ['44', '53'])).
% 42.50/42.71  thf('55', plain, ((m1_subset_1 @ sk_C_5 @ (k1_zfmisc_1 @ sk_A))),
% 42.50/42.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.50/42.71  thf(dt_k3_subset_1, axiom,
% 42.50/42.71    (![A:$i,B:$i]:
% 42.50/42.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 42.50/42.71       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 42.50/42.71  thf('56', plain,
% 42.50/42.71      (![X32 : $i, X33 : $i]:
% 42.50/42.71         ((m1_subset_1 @ (k3_subset_1 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))
% 42.50/42.71          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 42.50/42.71      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 42.50/42.71  thf('57', plain,
% 42.50/42.71      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_5) @ (k1_zfmisc_1 @ sk_A))),
% 42.50/42.71      inference('sup-', [status(thm)], ['55', '56'])).
% 42.50/42.71  thf('58', plain,
% 42.50/42.71      (![X26 : $i, X27 : $i]:
% 42.50/42.71         (~ (m1_subset_1 @ X26 @ X27)
% 42.50/42.71          | (r2_hidden @ X26 @ X27)
% 42.50/42.71          | (v1_xboole_0 @ X27))),
% 42.50/42.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 42.50/42.71  thf('59', plain,
% 42.50/42.71      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 42.50/42.71        | (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C_5) @ (k1_zfmisc_1 @ sk_A)))),
% 42.50/42.71      inference('sup-', [status(thm)], ['57', '58'])).
% 42.50/42.71  thf('60', plain,
% 42.50/42.71      (![X14 : $i, X16 : $i]:
% 42.50/42.71         ((r1_tarski @ X16 @ X14) | ~ (r2_hidden @ X16 @ (k1_zfmisc_1 @ X14)))),
% 42.50/42.71      inference('simplify', [status(thm)], ['13'])).
% 42.50/42.71  thf('61', plain,
% 42.50/42.71      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 42.50/42.71        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_5) @ sk_A))),
% 42.50/42.71      inference('sup-', [status(thm)], ['59', '60'])).
% 42.50/42.71  thf('62', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 42.50/42.71      inference('sup-', [status(thm)], ['20', '21'])).
% 42.50/42.71  thf('63', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_5) @ sk_A)),
% 42.50/42.71      inference('clc', [status(thm)], ['61', '62'])).
% 42.50/42.71  thf('64', plain,
% 42.50/42.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.50/42.71         (~ (r2_hidden @ X0 @ X1)
% 42.50/42.71          | (r2_hidden @ X0 @ X2)
% 42.50/42.71          | ~ (r1_tarski @ X1 @ X2))),
% 42.50/42.71      inference('cnf', [status(esa)], [d3_tarski])).
% 42.50/42.71  thf('65', plain,
% 42.50/42.71      (![X0 : $i]:
% 42.50/42.71         ((r2_hidden @ X0 @ sk_A)
% 42.50/42.71          | ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 42.50/42.71      inference('sup-', [status(thm)], ['63', '64'])).
% 42.50/42.71  thf('66', plain,
% 42.50/42.71      ((r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ sk_A)),
% 42.50/42.71      inference('sup-', [status(thm)], ['54', '65'])).
% 42.50/42.71  thf('67', plain,
% 42.50/42.71      (![X26 : $i, X27 : $i]:
% 42.50/42.71         ((m1_subset_1 @ X26 @ X27) | ~ (r2_hidden @ X26 @ X27))),
% 42.50/42.71      inference('clc', [status(thm)], ['27', '28'])).
% 42.50/42.71  thf('68', plain,
% 42.50/42.71      ((m1_subset_1 @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ sk_A)),
% 42.50/42.71      inference('sup-', [status(thm)], ['66', '67'])).
% 42.50/42.71  thf('69', plain,
% 42.50/42.71      (![X45 : $i]:
% 42.50/42.71         ((r2_hidden @ X45 @ sk_B)
% 42.50/42.71          | (r2_hidden @ X45 @ sk_C_5)
% 42.50/42.71          | ~ (m1_subset_1 @ X45 @ sk_A))),
% 42.50/42.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.50/42.71  thf('70', plain,
% 42.50/42.71      (((r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ sk_C_5)
% 42.50/42.71        | (r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ sk_B))),
% 42.50/42.71      inference('sup-', [status(thm)], ['68', '69'])).
% 42.50/42.71  thf('71', plain,
% 42.50/42.71      ((r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ 
% 42.50/42.71        (k3_subset_1 @ sk_A @ sk_C_5))),
% 42.50/42.71      inference('clc', [status(thm)], ['44', '53'])).
% 42.50/42.71  thf('72', plain,
% 42.50/42.71      (![X4 : $i, X6 : $i, X7 : $i]:
% 42.50/42.71         (~ (r2_hidden @ X6 @ X4)
% 42.50/42.71          | ~ (r2_hidden @ X6 @ X7)
% 42.50/42.71          | ~ (r1_xboole_0 @ X4 @ X7))),
% 42.50/42.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.50/42.71  thf('73', plain,
% 42.50/42.71      (![X0 : $i]:
% 42.50/42.71         (~ (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_5) @ X0)
% 42.50/42.71          | ~ (r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ X0))),
% 42.50/42.71      inference('sup-', [status(thm)], ['71', '72'])).
% 42.50/42.71  thf('74', plain,
% 42.50/42.71      (((r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ sk_B)
% 42.50/42.71        | ~ (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_5) @ sk_C_5))),
% 42.50/42.71      inference('sup-', [status(thm)], ['70', '73'])).
% 42.50/42.71  thf('75', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 42.50/42.71      inference('simplify', [status(thm)], ['16'])).
% 42.50/42.71  thf('76', plain, ((m1_subset_1 @ sk_C_5 @ (k1_zfmisc_1 @ sk_A))),
% 42.50/42.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.50/42.71  thf('77', plain,
% 42.50/42.71      (![X40 : $i, X41 : $i, X42 : $i]:
% 42.50/42.71         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 42.50/42.71          | ~ (r1_tarski @ X42 @ (k3_subset_1 @ X41 @ X40))
% 42.50/42.71          | (r1_xboole_0 @ X42 @ X40)
% 42.50/42.71          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 42.50/42.71      inference('cnf', [status(esa)], [t43_subset_1])).
% 42.50/42.71  thf('78', plain,
% 42.50/42.71      (![X0 : $i]:
% 42.50/42.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 42.50/42.71          | (r1_xboole_0 @ X0 @ sk_C_5)
% 42.50/42.71          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 42.50/42.71      inference('sup-', [status(thm)], ['76', '77'])).
% 42.50/42.71  thf('79', plain,
% 42.50/42.71      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_5) @ sk_C_5)
% 42.50/42.71        | ~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_5) @ (k1_zfmisc_1 @ sk_A)))),
% 42.50/42.71      inference('sup-', [status(thm)], ['75', '78'])).
% 42.50/42.71  thf('80', plain,
% 42.50/42.71      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_5) @ (k1_zfmisc_1 @ sk_A))),
% 42.50/42.71      inference('sup-', [status(thm)], ['55', '56'])).
% 42.50/42.71  thf('81', plain, ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_5) @ sk_C_5)),
% 42.50/42.72      inference('demod', [status(thm)], ['79', '80'])).
% 42.50/42.72  thf('82', plain,
% 42.50/42.72      ((r2_hidden @ (sk_C_4 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)) @ sk_B)),
% 42.50/42.72      inference('demod', [status(thm)], ['74', '81'])).
% 42.50/42.72  thf('83', plain,
% 42.50/42.72      (![X43 : $i, X44 : $i]:
% 42.50/42.72         (~ (r2_hidden @ (sk_C_4 @ X43 @ X44) @ X43)
% 42.50/42.72          | ((X44) = (X43))
% 42.50/42.72          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 42.50/42.72      inference('cnf', [status(esa)], [t49_subset_1])).
% 42.50/42.72  thf('84', plain,
% 42.50/42.72      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_A @ sk_C_5)))
% 42.50/42.72        | ((k3_subset_1 @ sk_A @ sk_C_5) = (sk_B)))),
% 42.50/42.72      inference('sup-', [status(thm)], ['82', '83'])).
% 42.50/42.72  thf('85', plain,
% 42.50/42.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 42.50/42.72      inference('sup-', [status(thm)], ['36', '37'])).
% 42.50/42.72  thf('86', plain, (((k3_subset_1 @ sk_A @ sk_C_5) = (sk_B))),
% 42.50/42.72      inference('demod', [status(thm)], ['84', '85'])).
% 42.50/42.72  thf('87', plain, (((sk_B) != (k3_subset_1 @ sk_A @ sk_C_5))),
% 42.50/42.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.50/42.72  thf('88', plain, ($false),
% 42.50/42.72      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 42.50/42.72  
% 42.50/42.72  % SZS output end Refutation
% 42.50/42.72  
% 42.53/42.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
