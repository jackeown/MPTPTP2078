%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5Rj4U4G7Mr

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:34 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 428 expanded)
%              Number of leaves         :   31 ( 133 expanded)
%              Depth                    :   18
%              Number of atoms          :  904 (3548 expanded)
%              Number of equality atoms :   98 ( 365 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X33 @ ( k3_subset_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('8',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('27',plain,(
    ! [X28: $i] :
      ( ( k2_subset_1 @ X28 )
      = X28 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('28',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('29',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_B )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('37',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('38',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('40',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['18','38','39'])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['16','40'])).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('44',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X31 ) @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('45',plain,(
    ! [X28: $i] :
      ( ( k2_subset_1 @ X28 )
      = X28 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('46',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X36 @ X35 ) @ ( k3_subset_1 @ X36 @ X37 ) )
      | ( r1_tarski @ X37 @ X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['43','55'])).

thf('57',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','64'])).

thf('66',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','65'])).

thf('67',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('68',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['16','40'])).

thf('69',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('70',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('74',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('75',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('77',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('78',plain,
    ( ( ( k2_xboole_0 @ sk_B @ sk_A )
      = sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['18','38','39'])).

thf('80',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['72','80'])).

thf('82',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('83',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','81','82'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('84',plain,(
    ! [X27: $i] :
      ( ( k1_subset_1 @ X27 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('85',plain,(
    ! [X34: $i] :
      ( ( k2_subset_1 @ X34 )
      = ( k3_subset_1 @ X34 @ ( k1_subset_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('86',plain,(
    ! [X28: $i] :
      ( ( k2_subset_1 @ X28 )
      = X28 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('87',plain,(
    ! [X34: $i] :
      ( X34
      = ( k3_subset_1 @ X34 @ ( k1_subset_1 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['84','87'])).

thf('89',plain,(
    sk_A = sk_B ),
    inference(demod,[status(thm)],['6','83','88'])).

thf('90',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('91',plain,(
    ! [X28: $i] :
      ( ( k2_subset_1 @ X28 )
      = X28 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('92',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['18','38'])).

thf('94',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['89','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5Rj4U4G7Mr
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 367 iterations in 0.115s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.37/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.37/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(t39_subset_1, conjecture,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.57       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.37/0.57         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i,B:$i]:
% 0.37/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.57          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.37/0.57            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.37/0.57  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(involutiveness_k3_subset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.57       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (![X32 : $i, X33 : $i]:
% 0.37/0.57         (((k3_subset_1 @ X33 @ (k3_subset_1 @ X33 @ X32)) = (X32))
% 0.37/0.57          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 0.37/0.57      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.57  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(d5_subset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.57       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (![X29 : $i, X30 : $i]:
% 0.37/0.57         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 0.37/0.57          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['2', '5'])).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.37/0.57        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.37/0.57         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.37/0.57      inference('split', [status(esa)], ['8'])).
% 0.37/0.57  thf(t28_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      ((((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.37/0.57          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.37/0.57         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.37/0.57          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.37/0.57         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      ((((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.37/0.57          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.37/0.57         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['7', '13'])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      ((((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.37/0.57          = (k4_xboole_0 @ sk_A @ sk_B)))
% 0.37/0.57         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.37/0.57        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.37/0.57       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.37/0.57      inference('split', [status(esa)], ['17'])).
% 0.37/0.57  thf(d10_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.57  thf('20', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.37/0.57      inference('simplify', [status(thm)], ['19'])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.57  thf('22', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.57  thf(t100_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (![X5 : $i, X6 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.57           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.57  thf(t92_xboole_1, axiom,
% 0.37/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.57  thf('25', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.57  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.37/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.37/0.57  thf('27', plain, (![X28 : $i]: ((k2_subset_1 @ X28) = (X28))),
% 0.37/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.37/0.57      inference('split', [status(esa)], ['8'])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.37/0.57         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.37/0.57      inference('split', [status(esa)], ['17'])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B))
% 0.37/0.57         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_B))
% 0.37/0.57         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.37/0.57             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['29', '32'])).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_A))
% 0.37/0.57         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.37/0.57             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.37/0.57      inference('demod', [status(thm)], ['33', '34'])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.37/0.57         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.37/0.57             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['26', '35'])).
% 0.37/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.57  thf('37', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.57  thf('38', plain,
% 0.37/0.57      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.37/0.57       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.37/0.57       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['8'])).
% 0.37/0.57  thf('40', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['18', '38', '39'])).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.37/0.57         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('simpl_trail', [status(thm)], ['16', '40'])).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      (![X5 : $i, X6 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.57           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('43', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(dt_k2_subset_1, axiom,
% 0.37/0.57    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      (![X31 : $i]: (m1_subset_1 @ (k2_subset_1 @ X31) @ (k1_zfmisc_1 @ X31))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.37/0.57  thf('45', plain, (![X28 : $i]: ((k2_subset_1 @ X28) = (X28))),
% 0.37/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.37/0.57  thf('46', plain, (![X31 : $i]: (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X31))),
% 0.37/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.37/0.57  thf('47', plain,
% 0.37/0.57      (![X29 : $i, X30 : $i]:
% 0.37/0.57         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 0.37/0.57          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.37/0.57  thf('48', plain,
% 0.37/0.57      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.37/0.57  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.37/0.57  thf('50', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['48', '49'])).
% 0.37/0.57  thf(t31_subset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.57       ( ![C:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.57           ( ( r1_tarski @ B @ C ) <=>
% 0.37/0.57             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.57  thf('51', plain,
% 0.37/0.57      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.37/0.57          | ~ (r1_tarski @ (k3_subset_1 @ X36 @ X35) @ 
% 0.37/0.57               (k3_subset_1 @ X36 @ X37))
% 0.37/0.57          | (r1_tarski @ X37 @ X35)
% 0.37/0.57          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.37/0.57  thf('52', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ X1 @ X0))
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.37/0.57          | (r1_tarski @ X0 @ X1)
% 0.37/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.57  thf('53', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.57  thf('54', plain, (![X31 : $i]: (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X31))),
% 0.37/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.37/0.57  thf('55', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (r1_tarski @ X0 @ X1))),
% 0.37/0.57      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.37/0.57  thf('56', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.37/0.57      inference('sup-', [status(thm)], ['43', '55'])).
% 0.37/0.57  thf('57', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.57  thf('58', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.57  thf('59', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.57  thf('60', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['58', '59'])).
% 0.37/0.57  thf('61', plain,
% 0.37/0.57      (![X5 : $i, X6 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.57           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('62', plain,
% 0.37/0.57      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup+', [status(thm)], ['60', '61'])).
% 0.37/0.57  thf(t91_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.57       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.37/0.57  thf('63', plain,
% 0.37/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.37/0.57           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.57  thf('64', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.37/0.57           = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ X0)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['62', '63'])).
% 0.37/0.57  thf('65', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.37/0.57           (k3_xboole_0 @ sk_B @ X0))
% 0.37/0.57           = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['42', '64'])).
% 0.37/0.57  thf('66', plain,
% 0.37/0.57      (((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.37/0.57         (k4_xboole_0 @ sk_A @ sk_B))
% 0.37/0.57         = (k5_xboole_0 @ sk_A @ 
% 0.37/0.57            (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['41', '65'])).
% 0.37/0.57  thf('67', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.57  thf('68', plain,
% 0.37/0.57      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.37/0.57         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('simpl_trail', [status(thm)], ['16', '40'])).
% 0.37/0.57  thf('69', plain,
% 0.37/0.57      (![X5 : $i, X6 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.57           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('70', plain,
% 0.37/0.57      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.37/0.57         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['68', '69'])).
% 0.37/0.57  thf(t98_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.37/0.57  thf('71', plain,
% 0.37/0.57      (![X18 : $i, X19 : $i]:
% 0.37/0.57         ((k2_xboole_0 @ X18 @ X19)
% 0.37/0.57           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.37/0.57  thf('72', plain,
% 0.37/0.57      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.37/0.57         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['70', '71'])).
% 0.37/0.57  thf('73', plain,
% 0.37/0.57      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.37/0.57          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.37/0.57         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.57  thf(t22_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.37/0.57  thf('74', plain,
% 0.37/0.57      (![X7 : $i, X8 : $i]:
% 0.37/0.57         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.37/0.57  thf('75', plain,
% 0.37/0.57      ((((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.37/0.57         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['73', '74'])).
% 0.37/0.57  thf('76', plain,
% 0.37/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.57  thf(t39_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.57  thf('77', plain,
% 0.37/0.57      (![X12 : $i, X13 : $i]:
% 0.37/0.57         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.37/0.57           = (k2_xboole_0 @ X12 @ X13))),
% 0.37/0.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.57  thf('78', plain,
% 0.37/0.57      ((((k2_xboole_0 @ sk_B @ sk_A) = (sk_B)))
% 0.37/0.57         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.37/0.57  thf('79', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['18', '38', '39'])).
% 0.37/0.57  thf('80', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.37/0.57      inference('simpl_trail', [status(thm)], ['78', '79'])).
% 0.37/0.57  thf('81', plain,
% 0.37/0.57      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['72', '80'])).
% 0.37/0.57  thf('82', plain,
% 0.37/0.57      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup+', [status(thm)], ['60', '61'])).
% 0.37/0.57  thf('83', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['66', '67', '81', '82'])).
% 0.37/0.57  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.57  thf('84', plain, (![X27 : $i]: ((k1_subset_1 @ X27) = (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.37/0.57  thf(t22_subset_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.37/0.57  thf('85', plain,
% 0.37/0.57      (![X34 : $i]:
% 0.37/0.57         ((k2_subset_1 @ X34) = (k3_subset_1 @ X34 @ (k1_subset_1 @ X34)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.37/0.57  thf('86', plain, (![X28 : $i]: ((k2_subset_1 @ X28) = (X28))),
% 0.37/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.37/0.57  thf('87', plain,
% 0.37/0.57      (![X34 : $i]: ((X34) = (k3_subset_1 @ X34 @ (k1_subset_1 @ X34)))),
% 0.37/0.57      inference('demod', [status(thm)], ['85', '86'])).
% 0.37/0.57  thf('88', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['84', '87'])).
% 0.37/0.57  thf('89', plain, (((sk_A) = (sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['6', '83', '88'])).
% 0.37/0.57  thf('90', plain,
% 0.37/0.57      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.37/0.57         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.37/0.57      inference('split', [status(esa)], ['17'])).
% 0.37/0.57  thf('91', plain, (![X28 : $i]: ((k2_subset_1 @ X28) = (X28))),
% 0.37/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.37/0.57  thf('92', plain,
% 0.37/0.57      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.37/0.57      inference('demod', [status(thm)], ['90', '91'])).
% 0.37/0.57  thf('93', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['18', '38'])).
% 0.37/0.57  thf('94', plain, (((sk_B) != (sk_A))),
% 0.37/0.57      inference('simpl_trail', [status(thm)], ['92', '93'])).
% 0.37/0.57  thf('95', plain, ($false),
% 0.37/0.57      inference('simplify_reflect-', [status(thm)], ['89', '94'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
