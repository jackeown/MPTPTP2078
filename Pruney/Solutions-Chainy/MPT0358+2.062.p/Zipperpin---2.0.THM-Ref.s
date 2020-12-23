%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m4zAIxY4Kh

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:30 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 555 expanded)
%              Number of leaves         :   22 ( 154 expanded)
%              Depth                    :   18
%              Number of atoms          :  662 (4858 expanded)
%              Number of equality atoms :   63 ( 494 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('1',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( ( k1_subset_1 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('6',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('7',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('12',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('14',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['4','12','13'])).

thf('15',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['2','14'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['22','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('33',plain,(
    ! [X14: $i] :
      ( ( k1_subset_1 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('34',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','12'])).

thf('36',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('48',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['37','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('52',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) )
    = ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('64',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','25'])).

thf('65',plain,
    ( ( k5_xboole_0 @ sk_B_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('68',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['62','65'])).

thf('72',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['34','35'])).

thf('74',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['55','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m4zAIxY4Kh
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 120 iterations in 0.052s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.37/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(t7_xboole_0, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.55  thf(t38_subset_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.37/0.55         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i]:
% 0.37/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.37/0.55            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.37/0.55        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.37/0.55         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.37/0.55      inference('split', [status(esa)], ['1'])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.37/0.55        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.37/0.55       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.55      inference('split', [status(esa)], ['3'])).
% 0.37/0.55  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('5', plain, (![X14 : $i]: ((k1_subset_1 @ X14) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.37/0.55         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.55      inference('split', [status(esa)], ['1'])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.37/0.55         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.37/0.55      inference('split', [status(esa)], ['3'])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.37/0.55         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.37/0.55             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.55  thf('11', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.37/0.55       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.37/0.55       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.37/0.55      inference('split', [status(esa)], ['1'])).
% 0.37/0.55  thf('14', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['4', '12', '13'])).
% 0.37/0.55  thf('15', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['2', '14'])).
% 0.37/0.55  thf(t28_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X9 : $i, X10 : $i]:
% 0.37/0.55         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.37/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf(t48_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.55           = (k3_xboole_0 @ X12 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.55  thf(d5_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.37/0.55       ( ![D:$i]:
% 0.37/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.37/0.55          | ~ (r2_hidden @ X4 @ X2)
% 0.37/0.55          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X4 @ X2)
% 0.37/0.55          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.55          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['18', '20'])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.37/0.55          | ~ (r2_hidden @ X0 @ 
% 0.37/0.55               (k4_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['17', '21'])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.37/0.55          | (r2_hidden @ X4 @ X1)
% 0.37/0.55          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.55         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ~ (r2_hidden @ X0 @ 
% 0.37/0.55            (k4_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.55      inference('clc', [status(thm)], ['22', '24'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (((k4_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['0', '25'])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.55          | (r2_hidden @ X0 @ X2)
% 0.37/0.55          | (r2_hidden @ X0 @ X3)
% 0.37/0.55          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.37/0.55          | (r2_hidden @ X0 @ X2)
% 0.37/0.55          | ~ (r2_hidden @ X0 @ X1))),
% 0.37/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((X0) = (k1_xboole_0))
% 0.37/0.55          | (r2_hidden @ (sk_B @ X0) @ X1)
% 0.37/0.55          | (r2_hidden @ (sk_B @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['27', '29'])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (((r2_hidden @ (sk_B @ sk_B_1) @ k1_xboole_0)
% 0.37/0.55        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['26', '30'])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.37/0.55         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.55      inference('split', [status(esa)], ['3'])).
% 0.37/0.55  thf('33', plain, (![X14 : $i]: ((k1_subset_1 @ X14) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.55  thf('35', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['4', '12'])).
% 0.37/0.55  thf('36', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['34', '35'])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      (((r2_hidden @ (sk_B @ sk_B_1) @ k1_xboole_0)
% 0.37/0.55        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['31', '36'])).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.55           = (k3_xboole_0 @ X12 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.55  thf('39', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X9 : $i, X10 : $i]:
% 0.37/0.55         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.37/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.55  thf('42', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.55          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['18', '20'])).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.37/0.55          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.55         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.37/0.55  thf('45', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.55      inference('clc', [status(thm)], ['43', '44'])).
% 0.37/0.55  thf('46', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['38', '45'])).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.55  thf('48', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.37/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.37/0.55  thf('49', plain,
% 0.37/0.55      ((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.37/0.55      inference('clc', [status(thm)], ['37', '48'])).
% 0.37/0.55  thf('50', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(d5_subset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.37/0.55  thf('51', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i]:
% 0.37/0.55         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 0.37/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.37/0.55  thf('52', plain,
% 0.37/0.55      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.55  thf('53', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X4 @ X2)
% 0.37/0.55          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.37/0.55  thf('54', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.37/0.55          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.55  thf('55', plain, (~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.37/0.55      inference('sup-', [status(thm)], ['49', '54'])).
% 0.37/0.55  thf('56', plain,
% 0.37/0.55      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf(t100_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.55  thf('57', plain,
% 0.37/0.55      (![X7 : $i, X8 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X7 @ X8)
% 0.37/0.55           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.55  thf('58', plain,
% 0.37/0.55      (((k4_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.37/0.55         = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['56', '57'])).
% 0.37/0.55  thf('59', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.55           = (k3_xboole_0 @ X12 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.55  thf('60', plain,
% 0.37/0.55      (((k4_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_B_1 @ sk_B_1))
% 0.37/0.55         = (k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['58', '59'])).
% 0.37/0.55  thf('61', plain,
% 0.37/0.55      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf('62', plain,
% 0.37/0.55      (((k4_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_B_1 @ sk_B_1)) = (sk_B_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['60', '61'])).
% 0.37/0.55  thf('63', plain,
% 0.37/0.55      (((k4_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.37/0.55         = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['56', '57'])).
% 0.37/0.55  thf('64', plain,
% 0.37/0.55      (((k4_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['0', '25'])).
% 0.37/0.55  thf('65', plain, (((k5_xboole_0 @ sk_B_1 @ sk_B_1) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['63', '64'])).
% 0.37/0.55  thf('66', plain, (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (sk_B_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['62', '65'])).
% 0.37/0.55  thf('67', plain,
% 0.37/0.55      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.55  thf('68', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.55         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.37/0.55  thf('69', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.55          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['67', '68'])).
% 0.37/0.55  thf('70', plain,
% 0.37/0.55      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)
% 0.37/0.55        | ((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['66', '69'])).
% 0.37/0.55  thf('71', plain, (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (sk_B_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['62', '65'])).
% 0.37/0.55  thf('72', plain,
% 0.37/0.55      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.37/0.55  thf('73', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['34', '35'])).
% 0.37/0.55  thf('74', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 0.37/0.55  thf('75', plain, ($false), inference('demod', [status(thm)], ['55', '74'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
