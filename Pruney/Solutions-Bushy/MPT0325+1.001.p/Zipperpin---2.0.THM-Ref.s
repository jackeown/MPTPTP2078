%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0325+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k8kORjRH9l

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:42 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 187 expanded)
%              Number of leaves         :   15 (  58 expanded)
%              Depth                    :   33
%              Number of atoms          :  775 (1950 expanded)
%              Number of equality atoms :  126 ( 237 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t138_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
       => ( ( ( k2_zfmisc_1 @ A @ B )
            = k1_xboole_0 )
          | ( ( r1_tarski @ A @ C )
            & ( r1_tarski @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t138_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
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
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X5 @ X7 ) @ ( k3_xboole_0 @ X6 @ X8 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('7',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t134_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X10 @ X9 )
       != ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( X0
        = ( k3_xboole_0 @ sk_D @ sk_B ) )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference(eq_res,[status(thm)],['9'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('12',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('16',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X5 @ X7 ) @ ( k3_xboole_0 @ X6 @ X8 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('24',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X10 @ X9 )
       != ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ( X10 = X11 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( X1
        = ( k3_xboole_0 @ sk_A @ sk_A ) )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = ( k3_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = ( k3_xboole_0 @ sk_A @ sk_A ) )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( X1
        = ( k3_xboole_0 @ sk_A @ sk_A ) )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['29'])).

thf('31',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_C @ sk_A ) )
    | ( ( k3_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('32',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('33',plain,
    ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ k1_xboole_0 )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( sk_A
      = ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('35',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( sk_A
      = ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','35'])).

thf('37',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( sk_A
      = ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('40',plain,
    ( ( r1_tarski @ sk_A @ sk_C )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('42',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['42','44'])).

thf('46',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['13'])).

thf('49',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('53',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('58',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['13'])).

thf('61',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['14','61'])).

thf('63',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['12','62'])).

thf('64',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('70',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','68','69'])).

thf('71',plain,(
    $false ),
    inference(simplify,[status(thm)],['70'])).


%------------------------------------------------------------------------------
