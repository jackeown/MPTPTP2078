%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GeZiBPvH4W

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 375 expanded)
%              Number of leaves         :   24 ( 108 expanded)
%              Depth                    :   16
%              Number of atoms          :  662 (3217 expanded)
%              Number of equality atoms :   67 ( 343 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('0',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X27: $i] :
      ( ( k1_subset_1 @ X27 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('7',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( ( k3_subset_1 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,
    ( ( ( k3_subset_1 @ sk_A @ k1_xboole_0 )
      = sk_A )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('16',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('19',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ( r2_hidden @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('23',plain,
    ( ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('24',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('25',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( r1_tarski @ X22 @ X20 )
      | ( X21
       != ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('27',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X22 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['5','29','30'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['3','31'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('33',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('34',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['3','31'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X27: $i] :
      ( ( k1_subset_1 @ X27 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('41',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('42',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['5','29'])).

thf('44',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['42','43'])).

thf('45',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['39','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('48',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('49',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('50',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ( r2_hidden @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('57',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X22 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('59',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('63',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('64',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','65'])).

thf('67',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('68',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['42','43'])).

thf('70',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['52','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GeZiBPvH4W
% 0.15/0.34  % Computer   : n011.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 14:58:27 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 494 iterations in 0.124s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.58  thf(t38_subset_1, conjecture,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.58       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.21/0.58         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i,B:$i]:
% 0.21/0.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.58          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.21/0.58            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.21/0.58  thf('0', plain,
% 0.21/0.58      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.21/0.58        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.21/0.58         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf(t28_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.58  thf('2', plain,
% 0.21/0.58      (![X15 : $i, X16 : $i]:
% 0.21/0.58         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      ((((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 0.21/0.58         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.21/0.58        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.21/0.58       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.21/0.58      inference('split', [status(esa)], ['4'])).
% 0.21/0.58  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.58  thf('6', plain, (![X27 : $i]: ((k1_subset_1 @ X27) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.58  thf('7', plain,
% 0.21/0.58      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.21/0.58         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf('9', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.58         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.58  thf(d5_subset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.58       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X28 : $i, X29 : $i]:
% 0.21/0.58         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 0.21/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      ((((k3_subset_1 @ sk_A @ k1_xboole_0)
% 0.21/0.58          = (k4_xboole_0 @ sk_A @ k1_xboole_0)))
% 0.21/0.58         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.58  thf(t3_boole, axiom,
% 0.21/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.58  thf('13', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      ((((k3_subset_1 @ sk_A @ k1_xboole_0) = (sk_A)))
% 0.21/0.58         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.21/0.58         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.21/0.58      inference('split', [status(esa)], ['4'])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.21/0.58         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.21/0.58             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.21/0.58         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.21/0.58             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.21/0.58         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.21/0.58             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['14', '19'])).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.58         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.58  thf(d2_subset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.58       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      (![X24 : $i, X25 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X24 @ X25)
% 0.21/0.58          | (r2_hidden @ X24 @ X25)
% 0.21/0.58          | (v1_xboole_0 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.58         | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A))))
% 0.21/0.58         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.58  thf(fc1_subset_1, axiom,
% 0.21/0.58    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.58  thf('24', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (((r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.58         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.58  thf(d1_zfmisc_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X22 @ X21)
% 0.21/0.58          | (r1_tarski @ X22 @ X20)
% 0.21/0.58          | ((X21) != (k1_zfmisc_1 @ X20)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.58  thf('27', plain,
% 0.21/0.58      (![X20 : $i, X22 : $i]:
% 0.21/0.58         ((r1_tarski @ X22 @ X20) | ~ (r2_hidden @ X22 @ (k1_zfmisc_1 @ X20)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (((r1_tarski @ k1_xboole_0 @ sk_A))
% 0.21/0.58         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['25', '27'])).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.21/0.58       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['20', '28'])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.21/0.58       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('31', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['5', '29', '30'])).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['3', '31'])).
% 0.21/0.58  thf(t7_xboole_0, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.58          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.58  thf('33', plain,
% 0.21/0.58      (![X12 : $i]:
% 0.21/0.58         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.58      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.58  thf(d4_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.58       ( ![D:$i]:
% 0.21/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.58           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.58          | (r2_hidden @ X4 @ X2)
% 0.21/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.58         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.58  thf('36', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.58          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['33', '35'])).
% 0.21/0.58  thf('37', plain,
% 0.21/0.58      (((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.21/0.58        | ((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.21/0.58            = (k1_xboole_0)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['32', '36'])).
% 0.21/0.58  thf('38', plain,
% 0.21/0.58      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['3', '31'])).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      (((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.21/0.58        | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.58  thf('40', plain, (![X27 : $i]: ((k1_subset_1 @ X27) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.21/0.58         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('split', [status(esa)], ['4'])).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.58  thf('43', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['5', '29'])).
% 0.21/0.58  thf('44', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['42', '43'])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      ((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['39', '44'])).
% 0.21/0.58  thf('46', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      (![X28 : $i, X29 : $i]:
% 0.21/0.58         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 0.21/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.58  thf('48', plain,
% 0.21/0.58      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.58  thf(d5_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.58       ( ![D:$i]:
% 0.21/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.58           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.58  thf('49', plain,
% 0.21/0.58      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.58          | ~ (r2_hidden @ X10 @ X8)
% 0.21/0.58          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X10 @ X8)
% 0.21/0.58          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.58  thf('51', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.21/0.58          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['48', '50'])).
% 0.21/0.58  thf('52', plain, (~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.21/0.58      inference('sup-', [status(thm)], ['45', '51'])).
% 0.21/0.58  thf('53', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('54', plain,
% 0.21/0.58      (![X24 : $i, X25 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X24 @ X25)
% 0.21/0.58          | (r2_hidden @ X24 @ X25)
% 0.21/0.58          | (v1_xboole_0 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.58  thf('55', plain,
% 0.21/0.58      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.58        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.58  thf('56', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.58  thf('57', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.58      inference('clc', [status(thm)], ['55', '56'])).
% 0.21/0.58  thf('58', plain,
% 0.21/0.58      (![X20 : $i, X22 : $i]:
% 0.21/0.58         ((r1_tarski @ X22 @ X20) | ~ (r2_hidden @ X22 @ (k1_zfmisc_1 @ X20)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.58  thf('59', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.21/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.58  thf('60', plain,
% 0.21/0.58      (![X15 : $i, X16 : $i]:
% 0.21/0.58         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.58  thf('61', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.58  thf('62', plain,
% 0.21/0.58      (![X12 : $i]:
% 0.21/0.58         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.58      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.58  thf('63', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.58          | (r2_hidden @ X4 @ X1)
% 0.21/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.58  thf('64', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.58         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['63'])).
% 0.21/0.58  thf('65', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.58          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['62', '64'])).
% 0.21/0.58  thf('66', plain,
% 0.21/0.58      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)
% 0.21/0.58        | ((k3_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['61', '65'])).
% 0.21/0.58  thf('67', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.58  thf('68', plain,
% 0.21/0.58      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['66', '67'])).
% 0.21/0.58  thf('69', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['42', '43'])).
% 0.21/0.58  thf('70', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.21/0.58  thf('71', plain, ($false), inference('demod', [status(thm)], ['52', '70'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
