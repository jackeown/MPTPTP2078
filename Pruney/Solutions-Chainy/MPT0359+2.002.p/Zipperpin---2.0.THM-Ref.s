%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QJXKGDNeXS

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:31 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 361 expanded)
%              Number of leaves         :   33 ( 122 expanded)
%              Depth                    :   17
%              Number of atoms          :  866 (2729 expanded)
%              Number of equality atoms :   89 ( 270 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X37 ) @ ( k1_zfmisc_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('2',plain,(
    ! [X34: $i] :
      ( ( k2_subset_1 @ X34 )
      = X34 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X37 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X35 @ X36 )
        = ( k4_xboole_0 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X35 @ X36 )
        = ( k6_subset_1 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X46 @ X45 ) @ ( k3_subset_1 @ X46 @ X47 ) )
      | ( r1_tarski @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_subset_1 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('16',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X37 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','17','18'])).

thf('20',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['0','19'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['22','23'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X35 @ X36 )
        = ( k6_subset_1 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('33',plain,
    ( ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['29','37'])).

thf('39',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('41',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    ! [X34: $i] :
      ( ( k2_subset_1 @ X34 )
      = X34 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('45',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('46',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf('49',plain,
    ( ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_A ) @ sk_B )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('52',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('53',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('56',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['43','54','55'])).

thf('57',plain,
    ( ( k6_subset_1 @ sk_B @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['41','56'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('58',plain,(
    ! [X38: $i,X39: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('59',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','17','18'])).

thf('61',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ sk_B ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['22','23'])).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('65',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('69',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('70',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k6_subset_1 @ X19 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['67','72'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('74',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('75',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( ( k4_xboole_0 @ X6 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['73','79'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('81',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('82',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['80','85'])).

thf('87',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['26','86'])).

thf('88',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['42'])).

thf('89',plain,(
    ! [X34: $i] :
      ( ( k2_subset_1 @ X34 )
      = X34 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('90',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['43','54'])).

thf('92',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['87','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QJXKGDNeXS
% 0.16/0.37  % Computer   : n015.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 14:26:38 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.68/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.92  % Solved by: fo/fo7.sh
% 0.68/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.92  % done 1608 iterations in 0.430s
% 0.68/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.92  % SZS output start Refutation
% 0.68/0.92  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.68/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.92  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.68/0.92  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.68/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.92  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.68/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.92  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.68/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.92  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.68/0.92  thf(t39_subset_1, conjecture,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.92       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.68/0.92         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.68/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.92    (~( ![A:$i,B:$i]:
% 0.68/0.92        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.92          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.68/0.92            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.68/0.92    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.68/0.92  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf(dt_k2_subset_1, axiom,
% 0.68/0.92    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.68/0.92  thf('1', plain,
% 0.68/0.92      (![X37 : $i]: (m1_subset_1 @ (k2_subset_1 @ X37) @ (k1_zfmisc_1 @ X37))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.68/0.92  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.68/0.92  thf('2', plain, (![X34 : $i]: ((k2_subset_1 @ X34) = (X34))),
% 0.68/0.92      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.68/0.92  thf('3', plain, (![X37 : $i]: (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X37))),
% 0.68/0.92      inference('demod', [status(thm)], ['1', '2'])).
% 0.68/0.92  thf(d5_subset_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.92       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.68/0.92  thf('4', plain,
% 0.68/0.92      (![X35 : $i, X36 : $i]:
% 0.68/0.92         (((k3_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))
% 0.68/0.92          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 0.68/0.92      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.68/0.92  thf(redefinition_k6_subset_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.68/0.92  thf('5', plain,
% 0.68/0.92      (![X42 : $i, X43 : $i]:
% 0.68/0.92         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 0.68/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.68/0.92  thf('6', plain,
% 0.68/0.92      (![X35 : $i, X36 : $i]:
% 0.68/0.92         (((k3_subset_1 @ X35 @ X36) = (k6_subset_1 @ X35 @ X36))
% 0.68/0.92          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 0.68/0.92      inference('demod', [status(thm)], ['4', '5'])).
% 0.68/0.92  thf('7', plain,
% 0.68/0.92      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k6_subset_1 @ X0 @ X0))),
% 0.68/0.92      inference('sup-', [status(thm)], ['3', '6'])).
% 0.68/0.92  thf(t31_subset_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.92       ( ![C:$i]:
% 0.68/0.92         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.92           ( ( r1_tarski @ B @ C ) <=>
% 0.68/0.92             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.68/0.92  thf('8', plain,
% 0.68/0.92      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.68/0.92         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 0.68/0.92          | ~ (r1_tarski @ (k3_subset_1 @ X46 @ X45) @ 
% 0.68/0.92               (k3_subset_1 @ X46 @ X47))
% 0.68/0.92          | (r1_tarski @ X47 @ X45)
% 0.68/0.92          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X46)))),
% 0.68/0.92      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.68/0.92  thf('9', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (r1_tarski @ (k6_subset_1 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1))
% 0.68/0.92          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.68/0.92          | (r1_tarski @ X1 @ X0)
% 0.68/0.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['7', '8'])).
% 0.68/0.92  thf(d10_xboole_0, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.92  thf('10', plain,
% 0.68/0.92      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.68/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.92  thf('11', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.68/0.92      inference('simplify', [status(thm)], ['10'])).
% 0.68/0.92  thf(l32_xboole_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.68/0.92  thf('12', plain,
% 0.68/0.92      (![X6 : $i, X8 : $i]:
% 0.68/0.92         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.68/0.92      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.68/0.92  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.92      inference('sup-', [status(thm)], ['11', '12'])).
% 0.68/0.92  thf('14', plain,
% 0.68/0.92      (![X42 : $i, X43 : $i]:
% 0.68/0.92         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 0.68/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.68/0.92  thf('15', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.92      inference('demod', [status(thm)], ['13', '14'])).
% 0.68/0.92  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.68/0.92  thf('16', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.68/0.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.92  thf('17', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X0) @ X1)),
% 0.68/0.92      inference('sup+', [status(thm)], ['15', '16'])).
% 0.68/0.92  thf('18', plain, (![X37 : $i]: (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X37))),
% 0.68/0.92      inference('demod', [status(thm)], ['1', '2'])).
% 0.68/0.92  thf('19', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)) | (r1_tarski @ X1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['9', '17', '18'])).
% 0.68/0.92  thf('20', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.68/0.92      inference('sup-', [status(thm)], ['0', '19'])).
% 0.68/0.92  thf(t28_xboole_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.68/0.92  thf('21', plain,
% 0.68/0.92      (![X13 : $i, X14 : $i]:
% 0.68/0.92         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.68/0.92      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.68/0.92  thf('22', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.68/0.92      inference('sup-', [status(thm)], ['20', '21'])).
% 0.68/0.92  thf(commutativity_k3_xboole_0, axiom,
% 0.68/0.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.68/0.92  thf('23', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.92  thf('24', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.68/0.92      inference('demod', [status(thm)], ['22', '23'])).
% 0.68/0.92  thf(t22_xboole_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.68/0.92  thf('25', plain,
% 0.68/0.92      (![X11 : $i, X12 : $i]:
% 0.68/0.92         ((k2_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)) = (X11))),
% 0.68/0.92      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.68/0.92  thf('26', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.68/0.92      inference('sup+', [status(thm)], ['24', '25'])).
% 0.68/0.92  thf('27', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('28', plain,
% 0.68/0.92      (![X35 : $i, X36 : $i]:
% 0.68/0.92         (((k3_subset_1 @ X35 @ X36) = (k6_subset_1 @ X35 @ X36))
% 0.68/0.92          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 0.68/0.92      inference('demod', [status(thm)], ['4', '5'])).
% 0.68/0.92  thf('29', plain,
% 0.68/0.92      (((k3_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.68/0.92      inference('sup-', [status(thm)], ['27', '28'])).
% 0.68/0.92  thf('30', plain,
% 0.68/0.92      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.68/0.92        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('31', plain,
% 0.68/0.92      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.68/0.92         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.68/0.92      inference('split', [status(esa)], ['30'])).
% 0.68/0.92  thf('32', plain,
% 0.68/0.92      (![X13 : $i, X14 : $i]:
% 0.68/0.92         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.68/0.92      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.68/0.92  thf('33', plain,
% 0.68/0.92      ((((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.68/0.92          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.68/0.92         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['31', '32'])).
% 0.68/0.92  thf('34', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.92  thf('35', plain,
% 0.68/0.92      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.68/0.92          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.68/0.92         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.68/0.92      inference('demod', [status(thm)], ['33', '34'])).
% 0.68/0.92  thf(t100_xboole_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.68/0.92  thf('36', plain,
% 0.68/0.92      (![X9 : $i, X10 : $i]:
% 0.68/0.92         ((k4_xboole_0 @ X9 @ X10)
% 0.68/0.92           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.68/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.68/0.92  thf('37', plain,
% 0.68/0.92      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.68/0.92          = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.68/0.92         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['35', '36'])).
% 0.68/0.92  thf('38', plain,
% 0.68/0.92      ((((k4_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ sk_B))
% 0.68/0.92          = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.68/0.92         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['29', '37'])).
% 0.68/0.92  thf('39', plain,
% 0.68/0.92      (![X42 : $i, X43 : $i]:
% 0.68/0.92         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 0.68/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.68/0.92  thf('40', plain,
% 0.68/0.92      (((k3_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.68/0.92      inference('sup-', [status(thm)], ['27', '28'])).
% 0.68/0.92  thf('41', plain,
% 0.68/0.92      ((((k6_subset_1 @ sk_B @ (k6_subset_1 @ sk_A @ sk_B))
% 0.68/0.92          = (k5_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ sk_B))))
% 0.68/0.92         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.68/0.92      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.68/0.92  thf('42', plain,
% 0.68/0.92      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.68/0.92        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('43', plain,
% 0.68/0.92      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.68/0.92       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.68/0.92      inference('split', [status(esa)], ['42'])).
% 0.68/0.92  thf('44', plain, (![X34 : $i]: ((k2_subset_1 @ X34) = (X34))),
% 0.68/0.92      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.68/0.92  thf('45', plain,
% 0.68/0.92      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.68/0.92      inference('split', [status(esa)], ['30'])).
% 0.68/0.92  thf('46', plain,
% 0.68/0.92      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.68/0.92      inference('sup+', [status(thm)], ['44', '45'])).
% 0.68/0.92  thf('47', plain,
% 0.68/0.92      (((k3_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.68/0.92      inference('sup-', [status(thm)], ['27', '28'])).
% 0.68/0.92  thf('48', plain,
% 0.68/0.92      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.68/0.92         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.68/0.92      inference('split', [status(esa)], ['42'])).
% 0.68/0.92  thf('49', plain,
% 0.68/0.92      ((~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.68/0.92         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['47', '48'])).
% 0.68/0.92  thf('50', plain,
% 0.68/0.92      ((~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_A) @ sk_B))
% 0.68/0.92         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.68/0.92             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.68/0.92      inference('sup-', [status(thm)], ['46', '49'])).
% 0.68/0.92  thf('51', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.92      inference('demod', [status(thm)], ['13', '14'])).
% 0.68/0.92  thf('52', plain,
% 0.68/0.92      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.68/0.92      inference('sup+', [status(thm)], ['44', '45'])).
% 0.68/0.92  thf('53', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.68/0.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.92  thf('54', plain,
% 0.68/0.92      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.68/0.92       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.68/0.92      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.68/0.92  thf('55', plain,
% 0.68/0.92      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.68/0.92       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.68/0.92      inference('split', [status(esa)], ['30'])).
% 0.68/0.92  thf('56', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.68/0.92      inference('sat_resolution*', [status(thm)], ['43', '54', '55'])).
% 0.68/0.92  thf('57', plain,
% 0.68/0.92      (((k6_subset_1 @ sk_B @ (k6_subset_1 @ sk_A @ sk_B))
% 0.68/0.92         = (k5_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ sk_B)))),
% 0.68/0.92      inference('simpl_trail', [status(thm)], ['41', '56'])).
% 0.68/0.92  thf(dt_k6_subset_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.68/0.92  thf('58', plain,
% 0.68/0.92      (![X38 : $i, X39 : $i]:
% 0.68/0.92         (m1_subset_1 @ (k6_subset_1 @ X38 @ X39) @ (k1_zfmisc_1 @ X38))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.68/0.92  thf('59', plain,
% 0.68/0.92      ((m1_subset_1 @ (k5_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ sk_B)) @ 
% 0.68/0.92        (k1_zfmisc_1 @ sk_B))),
% 0.68/0.92      inference('sup+', [status(thm)], ['57', '58'])).
% 0.68/0.92  thf('60', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)) | (r1_tarski @ X1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['9', '17', '18'])).
% 0.68/0.92  thf('61', plain,
% 0.68/0.92      ((r1_tarski @ (k5_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ sk_B)) @ sk_B)),
% 0.68/0.92      inference('sup-', [status(thm)], ['59', '60'])).
% 0.68/0.92  thf('62', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.68/0.92      inference('demod', [status(thm)], ['22', '23'])).
% 0.68/0.92  thf('63', plain,
% 0.68/0.92      (![X9 : $i, X10 : $i]:
% 0.68/0.92         ((k4_xboole_0 @ X9 @ X10)
% 0.68/0.92           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.68/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.68/0.92  thf('64', plain,
% 0.68/0.92      (![X42 : $i, X43 : $i]:
% 0.68/0.92         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 0.68/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.68/0.92  thf('65', plain,
% 0.68/0.92      (![X9 : $i, X10 : $i]:
% 0.68/0.92         ((k6_subset_1 @ X9 @ X10)
% 0.68/0.92           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.68/0.92      inference('demod', [status(thm)], ['63', '64'])).
% 0.68/0.92  thf('66', plain,
% 0.68/0.92      (((k6_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.92      inference('sup+', [status(thm)], ['62', '65'])).
% 0.68/0.92  thf('67', plain,
% 0.68/0.92      ((r1_tarski @ (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) @ sk_B)),
% 0.68/0.92      inference('demod', [status(thm)], ['61', '66'])).
% 0.68/0.92  thf('68', plain,
% 0.68/0.92      (((k6_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.92      inference('sup+', [status(thm)], ['62', '65'])).
% 0.68/0.92  thf(t98_xboole_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.68/0.92  thf('69', plain,
% 0.68/0.92      (![X18 : $i, X19 : $i]:
% 0.68/0.92         ((k2_xboole_0 @ X18 @ X19)
% 0.68/0.92           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.68/0.92      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.68/0.92  thf('70', plain,
% 0.68/0.92      (![X42 : $i, X43 : $i]:
% 0.68/0.92         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 0.68/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.68/0.92  thf('71', plain,
% 0.68/0.92      (![X18 : $i, X19 : $i]:
% 0.68/0.92         ((k2_xboole_0 @ X18 @ X19)
% 0.68/0.92           = (k5_xboole_0 @ X18 @ (k6_subset_1 @ X19 @ X18)))),
% 0.68/0.92      inference('demod', [status(thm)], ['69', '70'])).
% 0.68/0.92  thf('72', plain,
% 0.68/0.92      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.68/0.92         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['68', '71'])).
% 0.68/0.92  thf('73', plain, ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 0.68/0.92      inference('demod', [status(thm)], ['67', '72'])).
% 0.68/0.92  thf(t46_xboole_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.68/0.92  thf('74', plain,
% 0.68/0.92      (![X16 : $i, X17 : $i]:
% 0.68/0.92         ((k4_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (k1_xboole_0))),
% 0.68/0.92      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.68/0.92  thf('75', plain,
% 0.68/0.92      (![X6 : $i, X7 : $i]:
% 0.68/0.92         ((r1_tarski @ X6 @ X7) | ((k4_xboole_0 @ X6 @ X7) != (k1_xboole_0)))),
% 0.68/0.92      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.68/0.92  thf('76', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((k1_xboole_0) != (k1_xboole_0))
% 0.68/0.92          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['74', '75'])).
% 0.68/0.92  thf('77', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.68/0.92      inference('simplify', [status(thm)], ['76'])).
% 0.68/0.92  thf('78', plain,
% 0.68/0.92      (![X3 : $i, X5 : $i]:
% 0.68/0.92         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.68/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.92  thf('79', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.68/0.92          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['77', '78'])).
% 0.68/0.92  thf('80', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.68/0.92      inference('sup-', [status(thm)], ['73', '79'])).
% 0.68/0.92  thf(commutativity_k2_tarski, axiom,
% 0.68/0.92    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.68/0.92  thf('81', plain,
% 0.68/0.92      (![X20 : $i, X21 : $i]:
% 0.68/0.92         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 0.68/0.92      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.68/0.92  thf(l51_zfmisc_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.68/0.92  thf('82', plain,
% 0.68/0.92      (![X27 : $i, X28 : $i]:
% 0.68/0.92         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 0.68/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.68/0.92  thf('83', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.92      inference('sup+', [status(thm)], ['81', '82'])).
% 0.68/0.92  thf('84', plain,
% 0.68/0.92      (![X27 : $i, X28 : $i]:
% 0.68/0.92         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 0.68/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.68/0.92  thf('85', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.92      inference('sup+', [status(thm)], ['83', '84'])).
% 0.68/0.92  thf('86', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.68/0.92      inference('demod', [status(thm)], ['80', '85'])).
% 0.68/0.92  thf('87', plain, (((sk_A) = (sk_B))),
% 0.68/0.92      inference('sup+', [status(thm)], ['26', '86'])).
% 0.68/0.92  thf('88', plain,
% 0.68/0.92      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.68/0.92         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.68/0.92      inference('split', [status(esa)], ['42'])).
% 0.68/0.92  thf('89', plain, (![X34 : $i]: ((k2_subset_1 @ X34) = (X34))),
% 0.68/0.92      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.68/0.92  thf('90', plain,
% 0.68/0.92      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.68/0.92      inference('demod', [status(thm)], ['88', '89'])).
% 0.68/0.92  thf('91', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.68/0.92      inference('sat_resolution*', [status(thm)], ['43', '54'])).
% 0.68/0.92  thf('92', plain, (((sk_B) != (sk_A))),
% 0.68/0.92      inference('simpl_trail', [status(thm)], ['90', '91'])).
% 0.68/0.92  thf('93', plain, ($false),
% 0.68/0.92      inference('simplify_reflect-', [status(thm)], ['87', '92'])).
% 0.68/0.92  
% 0.68/0.92  % SZS output end Refutation
% 0.68/0.92  
% 0.68/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
