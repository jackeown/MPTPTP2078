%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NZWiw7GL6f

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 422 expanded)
%              Number of leaves         :   30 ( 139 expanded)
%              Depth                    :   19
%              Number of atoms          :  922 (3265 expanded)
%              Number of equality atoms :   95 ( 338 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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

thf('0',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('15',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('22',plain,
    ( ( ( k2_xboole_0 @ sk_B @ sk_A )
      = ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_A ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['15','18','19','20','21'])).

thf('23',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['23'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('25',plain,(
    ! [X33: $i] :
      ( ( k2_subset_1 @ X33 )
      = X33 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('26',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['23'])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_B )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('39',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('44',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('45',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','37','42','43','44'])).

thf('46',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['24','45','46'])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['22','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('54',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('60',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('61',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('66',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X36 ) @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('67',plain,(
    ! [X33: $i] :
      ( ( k2_subset_1 @ X33 )
      = X33 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('68',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('73',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X41 @ X40 ) @ ( k3_subset_1 @ X41 @ X42 ) )
      | ( r1_tarski @ X42 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('76',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','77','78'])).

thf('80',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['65','79'])).

thf('81',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('82',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['82','83'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('85',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('86',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['65','79'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('89',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['84','85'])).

thf('90',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['59','64','86','87','88','89'])).

thf('91',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('92',plain,(
    ! [X33: $i] :
      ( ( k2_subset_1 @ X33 )
      = X33 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('93',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['24','45'])).

thf('95',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['90','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NZWiw7GL6f
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:29:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.63  % Solved by: fo/fo7.sh
% 0.20/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.63  % done 855 iterations in 0.168s
% 0.20/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.63  % SZS output start Refutation
% 0.20/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.63  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.63  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.63  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.63  thf(t39_subset_1, conjecture,
% 0.20/0.63    (![A:$i,B:$i]:
% 0.20/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.63       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.63         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.20/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.63    (~( ![A:$i,B:$i]:
% 0.20/0.63        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.63          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.63            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.20/0.63    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.20/0.63  thf('0', plain,
% 0.20/0.63      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.20/0.63        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.63  thf('1', plain,
% 0.20/0.63      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.63         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.63      inference('split', [status(esa)], ['0'])).
% 0.20/0.63  thf(t28_xboole_1, axiom,
% 0.20/0.63    (![A:$i,B:$i]:
% 0.20/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.63  thf('2', plain,
% 0.20/0.63      (![X12 : $i, X13 : $i]:
% 0.20/0.63         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.20/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.63  thf('3', plain,
% 0.20/0.63      ((((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.63          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.63         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.63  thf('4', plain,
% 0.20/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.63  thf('5', plain,
% 0.20/0.63      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.63          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.63         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.63      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.63  thf(t100_xboole_1, axiom,
% 0.20/0.63    (![A:$i,B:$i]:
% 0.20/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.63  thf('6', plain,
% 0.20/0.63      (![X8 : $i, X9 : $i]:
% 0.20/0.63         ((k4_xboole_0 @ X8 @ X9)
% 0.20/0.63           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.20/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.63  thf('7', plain,
% 0.20/0.63      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.63          = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.20/0.63         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.63      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.63  thf(t48_xboole_1, axiom,
% 0.20/0.63    (![A:$i,B:$i]:
% 0.20/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.63  thf('8', plain,
% 0.20/0.63      (![X15 : $i, X16 : $i]:
% 0.20/0.63         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.63           = (k3_xboole_0 @ X15 @ X16))),
% 0.20/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.63  thf('9', plain,
% 0.20/0.63      ((((k4_xboole_0 @ sk_B @ 
% 0.20/0.63          (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.63          = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.20/0.63         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.63      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.63  thf('10', plain,
% 0.20/0.63      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.63          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.63         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.63      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.63  thf('11', plain,
% 0.20/0.63      ((((k4_xboole_0 @ sk_B @ 
% 0.20/0.63          (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.63          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.63         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.63      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.63  thf('12', plain,
% 0.20/0.63      (![X15 : $i, X16 : $i]:
% 0.20/0.63         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.63           = (k3_xboole_0 @ X15 @ X16))),
% 0.20/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.63  thf('13', plain,
% 0.20/0.63      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.63          = (k3_xboole_0 @ sk_B @ 
% 0.20/0.63             (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))))
% 0.20/0.63         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.63  thf('14', plain,
% 0.20/0.63      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.63          = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.20/0.63         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.63      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.63  thf('15', plain,
% 0.20/0.63      ((((k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.63          = (k3_xboole_0 @ sk_B @ 
% 0.20/0.63             (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))))
% 0.20/0.63         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.63      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.63  thf('16', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.63  thf(d5_subset_1, axiom,
% 0.20/0.63    (![A:$i,B:$i]:
% 0.20/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.63       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.63  thf('17', plain,
% 0.20/0.63      (![X34 : $i, X35 : $i]:
% 0.20/0.63         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.20/0.63          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.20/0.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.63  thf('18', plain,
% 0.20/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.63  thf(t98_xboole_1, axiom,
% 0.20/0.63    (![A:$i,B:$i]:
% 0.20/0.63     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.63  thf('19', plain,
% 0.20/0.63      (![X17 : $i, X18 : $i]:
% 0.20/0.63         ((k2_xboole_0 @ X17 @ X18)
% 0.20/0.63           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.20/0.63      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.63  thf('20', plain,
% 0.20/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.63  thf('21', plain,
% 0.20/0.63      (![X17 : $i, X18 : $i]:
% 0.20/0.63         ((k2_xboole_0 @ X17 @ X18)
% 0.20/0.63           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.20/0.63      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.63  thf('22', plain,
% 0.20/0.63      ((((k2_xboole_0 @ sk_B @ sk_A)
% 0.20/0.63          = (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ sk_A))))
% 0.20/0.63         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.63      inference('demod', [status(thm)], ['15', '18', '19', '20', '21'])).
% 0.20/0.63  thf('23', plain,
% 0.20/0.63      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.20/0.63        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.63  thf('24', plain,
% 0.20/0.63      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.20/0.63       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.63      inference('split', [status(esa)], ['23'])).
% 0.20/0.63  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.63  thf('25', plain, (![X33 : $i]: ((k2_subset_1 @ X33) = (X33))),
% 0.20/0.63      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.63  thf('26', plain,
% 0.20/0.63      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.63      inference('split', [status(esa)], ['0'])).
% 0.20/0.63  thf('27', plain,
% 0.20/0.63      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.63      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.63  thf('28', plain,
% 0.20/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.63  thf('29', plain,
% 0.20/0.63      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.63         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.63      inference('split', [status(esa)], ['23'])).
% 0.20/0.63  thf('30', plain,
% 0.20/0.63      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.63         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.63      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.63  thf('31', plain,
% 0.20/0.63      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_B))
% 0.20/0.63         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.63             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.63      inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.63  thf(d10_xboole_0, axiom,
% 0.20/0.63    (![A:$i,B:$i]:
% 0.20/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.63  thf('32', plain,
% 0.20/0.63      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.20/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.63  thf('33', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.20/0.63      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.63  thf('34', plain,
% 0.20/0.63      (![X12 : $i, X13 : $i]:
% 0.20/0.63         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.20/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.63  thf('35', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.63      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.63  thf('36', plain,
% 0.20/0.63      (![X8 : $i, X9 : $i]:
% 0.20/0.63         ((k4_xboole_0 @ X8 @ X9)
% 0.20/0.63           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.20/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.63  thf('37', plain,
% 0.20/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.63      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.63  thf('38', plain,
% 0.20/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.63      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.63  thf('39', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.20/0.63      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.63  thf(l32_xboole_1, axiom,
% 0.20/0.63    (![A:$i,B:$i]:
% 0.20/0.63     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.63  thf('40', plain,
% 0.20/0.63      (![X5 : $i, X7 : $i]:
% 0.20/0.63         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.20/0.63      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.63  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.63  thf('42', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.63      inference('sup+', [status(thm)], ['38', '41'])).
% 0.20/0.63  thf('43', plain,
% 0.20/0.63      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.63      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.63  thf('44', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.20/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.63  thf('45', plain,
% 0.20/0.63      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.63       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.63      inference('demod', [status(thm)], ['31', '37', '42', '43', '44'])).
% 0.20/0.63  thf('46', plain,
% 0.20/0.63      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.63       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.63      inference('split', [status(esa)], ['0'])).
% 0.20/0.63  thf('47', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.63      inference('sat_resolution*', [status(thm)], ['24', '45', '46'])).
% 0.20/0.63  thf('48', plain,
% 0.20/0.63      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.20/0.63         = (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.20/0.63      inference('simpl_trail', [status(thm)], ['22', '47'])).
% 0.20/0.63  thf('49', plain,
% 0.20/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.63  thf('50', plain,
% 0.20/0.63      (![X8 : $i, X9 : $i]:
% 0.20/0.63         ((k4_xboole_0 @ X8 @ X9)
% 0.20/0.63           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.20/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.63  thf('51', plain,
% 0.20/0.63      (![X0 : $i, X1 : $i]:
% 0.20/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.63      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.63  thf('52', plain,
% 0.20/0.63      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B)
% 0.20/0.63         = (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 0.20/0.63            (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.20/0.63      inference('sup+', [status(thm)], ['48', '51'])).
% 0.20/0.63  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.63      inference('sup+', [status(thm)], ['38', '41'])).
% 0.20/0.63  thf('54', plain,
% 0.20/0.63      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.20/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.63  thf('55', plain,
% 0.20/0.63      (![X5 : $i, X6 : $i]:
% 0.20/0.63         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.20/0.63      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.63  thf('56', plain,
% 0.20/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.63        | (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.63      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.63  thf('57', plain, ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 0.20/0.63      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.63  thf('58', plain,
% 0.20/0.63      (![X2 : $i, X4 : $i]:
% 0.20/0.63         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.20/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.63  thf('59', plain,
% 0.20/0.63      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.20/0.63        | ((sk_B) = (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.20/0.63      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.63  thf(commutativity_k2_tarski, axiom,
% 0.20/0.63    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.63  thf('60', plain,
% 0.20/0.63      (![X19 : $i, X20 : $i]:
% 0.20/0.63         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 0.20/0.63      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.63  thf(l51_zfmisc_1, axiom,
% 0.20/0.63    (![A:$i,B:$i]:
% 0.20/0.63     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.63  thf('61', plain,
% 0.20/0.63      (![X30 : $i, X31 : $i]:
% 0.20/0.63         ((k3_tarski @ (k2_tarski @ X30 @ X31)) = (k2_xboole_0 @ X30 @ X31))),
% 0.20/0.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.63  thf('62', plain,
% 0.20/0.63      (![X0 : $i, X1 : $i]:
% 0.20/0.63         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.63      inference('sup+', [status(thm)], ['60', '61'])).
% 0.20/0.63  thf('63', plain,
% 0.20/0.63      (![X30 : $i, X31 : $i]:
% 0.20/0.63         ((k3_tarski @ (k2_tarski @ X30 @ X31)) = (k2_xboole_0 @ X30 @ X31))),
% 0.20/0.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.63  thf('64', plain,
% 0.20/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.63      inference('sup+', [status(thm)], ['62', '63'])).
% 0.20/0.63  thf('65', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.63  thf(dt_k2_subset_1, axiom,
% 0.20/0.63    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.63  thf('66', plain,
% 0.20/0.63      (![X36 : $i]: (m1_subset_1 @ (k2_subset_1 @ X36) @ (k1_zfmisc_1 @ X36))),
% 0.20/0.63      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.63  thf('67', plain, (![X33 : $i]: ((k2_subset_1 @ X33) = (X33))),
% 0.20/0.63      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.63  thf('68', plain, (![X36 : $i]: (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X36))),
% 0.20/0.63      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.63  thf('69', plain,
% 0.20/0.63      (![X34 : $i, X35 : $i]:
% 0.20/0.63         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.20/0.63          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.20/0.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.63  thf('70', plain,
% 0.20/0.63      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.63      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.63  thf('71', plain,
% 0.20/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.63      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.63  thf('72', plain,
% 0.20/0.63      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.63      inference('demod', [status(thm)], ['70', '71'])).
% 0.20/0.63  thf(t31_subset_1, axiom,
% 0.20/0.63    (![A:$i,B:$i]:
% 0.20/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.63       ( ![C:$i]:
% 0.20/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.63           ( ( r1_tarski @ B @ C ) <=>
% 0.20/0.63             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.63  thf('73', plain,
% 0.20/0.63      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.63         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.20/0.63          | ~ (r1_tarski @ (k3_subset_1 @ X41 @ X40) @ 
% 0.20/0.63               (k3_subset_1 @ X41 @ X42))
% 0.20/0.63          | (r1_tarski @ X42 @ X40)
% 0.20/0.63          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 0.20/0.63      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.20/0.63  thf('74', plain,
% 0.20/0.63      (![X0 : $i, X1 : $i]:
% 0.20/0.63         (~ (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1))
% 0.20/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.20/0.63          | (r1_tarski @ X1 @ X0)
% 0.20/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.63      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.63  thf('75', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.63      inference('sup+', [status(thm)], ['38', '41'])).
% 0.20/0.63  thf('76', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.20/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.63  thf('77', plain,
% 0.20/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.20/0.63      inference('sup+', [status(thm)], ['75', '76'])).
% 0.20/0.63  thf('78', plain, (![X36 : $i]: (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X36))),
% 0.20/0.63      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.63  thf('79', plain,
% 0.20/0.63      (![X0 : $i, X1 : $i]:
% 0.20/0.63         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)) | (r1_tarski @ X1 @ X0))),
% 0.20/0.63      inference('demod', [status(thm)], ['74', '77', '78'])).
% 0.20/0.63  thf('80', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.63      inference('sup-', [status(thm)], ['65', '79'])).
% 0.20/0.63  thf('81', plain,
% 0.20/0.63      (![X12 : $i, X13 : $i]:
% 0.20/0.63         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.20/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.63  thf('82', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.63      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.63  thf('83', plain,
% 0.20/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.63  thf('84', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.63      inference('demod', [status(thm)], ['82', '83'])).
% 0.20/0.63  thf(t22_xboole_1, axiom,
% 0.20/0.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.20/0.63  thf('85', plain,
% 0.20/0.63      (![X10 : $i, X11 : $i]:
% 0.20/0.63         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.20/0.63      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.20/0.63  thf('86', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.20/0.63      inference('sup+', [status(thm)], ['84', '85'])).
% 0.20/0.63  thf('87', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.63      inference('sup-', [status(thm)], ['65', '79'])).
% 0.20/0.63  thf('88', plain,
% 0.20/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.63      inference('sup+', [status(thm)], ['62', '63'])).
% 0.20/0.63  thf('89', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.20/0.63      inference('sup+', [status(thm)], ['84', '85'])).
% 0.20/0.63  thf('90', plain, (((sk_B) = (sk_A))),
% 0.20/0.63      inference('demod', [status(thm)], ['59', '64', '86', '87', '88', '89'])).
% 0.20/0.63  thf('91', plain,
% 0.20/0.63      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.20/0.63         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.63      inference('split', [status(esa)], ['23'])).
% 0.20/0.63  thf('92', plain, (![X33 : $i]: ((k2_subset_1 @ X33) = (X33))),
% 0.20/0.63      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.63  thf('93', plain,
% 0.20/0.63      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.63      inference('demod', [status(thm)], ['91', '92'])).
% 0.20/0.63  thf('94', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.63      inference('sat_resolution*', [status(thm)], ['24', '45'])).
% 0.20/0.63  thf('95', plain, (((sk_B) != (sk_A))),
% 0.20/0.63      inference('simpl_trail', [status(thm)], ['93', '94'])).
% 0.20/0.63  thf('96', plain, ($false),
% 0.20/0.63      inference('simplify_reflect-', [status(thm)], ['90', '95'])).
% 0.20/0.63  
% 0.20/0.63  % SZS output end Refutation
% 0.20/0.63  
% 0.20/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
