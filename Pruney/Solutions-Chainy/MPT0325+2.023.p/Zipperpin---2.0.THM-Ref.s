%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.spFBR3mB82

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:43 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 187 expanded)
%              Number of leaves         :   15 (  58 expanded)
%              Depth                    :   33
%              Number of atoms          :  775 (1950 expanded)
%              Number of equality atoms :  126 ( 237 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X9 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X14 @ X13 )
       != ( k2_zfmisc_1 @ X15 @ X16 ) )
      | ( X13 = X16 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
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
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X9 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('24',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X14 @ X13 )
       != ( k2_zfmisc_1 @ X15 @ X16 ) )
      | ( X14 = X15 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('35',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
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
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
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
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
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
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
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
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
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
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('70',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','68','69'])).

thf('71',plain,(
    $false ),
    inference(simplify,[status(thm)],['70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.spFBR3mB82
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:43:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.82/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.82/1.03  % Solved by: fo/fo7.sh
% 0.82/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.03  % done 765 iterations in 0.566s
% 0.82/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.82/1.03  % SZS output start Refutation
% 0.82/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.82/1.03  thf(sk_D_type, type, sk_D: $i).
% 0.82/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.82/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.03  thf(sk_C_type, type, sk_C: $i).
% 0.82/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.82/1.03  thf(t138_zfmisc_1, conjecture,
% 0.82/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.03     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.82/1.03       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.82/1.03         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.82/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.03    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.03        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.82/1.03          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.82/1.03            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.82/1.03    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.82/1.03  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('1', plain,
% 0.82/1.03      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(t28_xboole_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.82/1.03  thf('2', plain,
% 0.82/1.03      (![X4 : $i, X5 : $i]:
% 0.82/1.03         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.82/1.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.82/1.03  thf('3', plain,
% 0.82/1.03      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.82/1.03         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.82/1.03      inference('sup-', [status(thm)], ['1', '2'])).
% 0.82/1.03  thf(commutativity_k3_xboole_0, axiom,
% 0.82/1.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.82/1.03  thf('4', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.03  thf('5', plain,
% 0.82/1.03      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.82/1.03         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.82/1.03      inference('demod', [status(thm)], ['3', '4'])).
% 0.82/1.03  thf(t123_zfmisc_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.03     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.82/1.03       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.82/1.03  thf('6', plain,
% 0.82/1.03      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.82/1.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ X9 @ X11) @ (k3_xboole_0 @ X10 @ X12))
% 0.82/1.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X9 @ X10) @ 
% 0.82/1.03              (k2_zfmisc_1 @ X11 @ X12)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.82/1.03  thf('7', plain,
% 0.82/1.03      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.82/1.03         (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.82/1.03      inference('demod', [status(thm)], ['5', '6'])).
% 0.82/1.03  thf(t134_zfmisc_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.03     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.82/1.03       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.82/1.03         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.82/1.03  thf('8', plain,
% 0.82/1.03      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.82/1.03         (((X13) = (k1_xboole_0))
% 0.82/1.03          | ((X14) = (k1_xboole_0))
% 0.82/1.03          | ((k2_zfmisc_1 @ X14 @ X13) != (k2_zfmisc_1 @ X15 @ X16))
% 0.82/1.03          | ((X13) = (X16)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.82/1.03  thf('9', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (((k2_zfmisc_1 @ X1 @ X0) != (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.82/1.03          | ((X0) = (k3_xboole_0 @ sk_D @ sk_B))
% 0.82/1.03          | ((X1) = (k1_xboole_0))
% 0.82/1.03          | ((X0) = (k1_xboole_0)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['7', '8'])).
% 0.82/1.03  thf('10', plain,
% 0.82/1.03      ((((sk_B) = (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k1_xboole_0))
% 0.82/1.03        | ((sk_B) = (k3_xboole_0 @ sk_D @ sk_B)))),
% 0.82/1.03      inference('eq_res', [status(thm)], ['9'])).
% 0.82/1.03  thf(t17_xboole_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.82/1.03  thf('11', plain,
% 0.82/1.03      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.82/1.03      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.82/1.03  thf('12', plain,
% 0.82/1.03      (((r1_tarski @ sk_B @ sk_D)
% 0.82/1.03        | ((sk_A) = (k1_xboole_0))
% 0.82/1.03        | ((sk_B) = (k1_xboole_0)))),
% 0.82/1.03      inference('sup+', [status(thm)], ['10', '11'])).
% 0.82/1.03  thf('13', plain,
% 0.82/1.03      ((~ (r1_tarski @ sk_A @ sk_C) | ~ (r1_tarski @ sk_B @ sk_D))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('14', plain,
% 0.82/1.03      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.82/1.03      inference('split', [status(esa)], ['13'])).
% 0.82/1.03  thf('15', plain,
% 0.82/1.03      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.82/1.03         (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.82/1.03      inference('demod', [status(thm)], ['5', '6'])).
% 0.82/1.03  thf('16', plain,
% 0.82/1.03      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.82/1.03         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.82/1.03      inference('demod', [status(thm)], ['3', '4'])).
% 0.82/1.03  thf('17', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.03  thf('18', plain,
% 0.82/1.03      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.82/1.03      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.82/1.03  thf('19', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.82/1.03      inference('sup+', [status(thm)], ['17', '18'])).
% 0.82/1.03  thf('20', plain,
% 0.82/1.03      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.82/1.03      inference('sup+', [status(thm)], ['16', '19'])).
% 0.82/1.03  thf('21', plain,
% 0.82/1.03      (![X4 : $i, X5 : $i]:
% 0.82/1.03         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.82/1.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.82/1.03  thf('22', plain,
% 0.82/1.03      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.82/1.03         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.82/1.03      inference('sup-', [status(thm)], ['20', '21'])).
% 0.82/1.03  thf('23', plain,
% 0.82/1.03      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.82/1.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ X9 @ X11) @ (k3_xboole_0 @ X10 @ X12))
% 0.82/1.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X9 @ X10) @ 
% 0.82/1.03              (k2_zfmisc_1 @ X11 @ X12)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.82/1.03  thf('24', plain,
% 0.82/1.03      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_A) @ 
% 0.82/1.03         (k3_xboole_0 @ sk_B @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.82/1.03      inference('demod', [status(thm)], ['22', '23'])).
% 0.82/1.03  thf('25', plain,
% 0.82/1.03      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.82/1.03         (((X13) = (k1_xboole_0))
% 0.82/1.03          | ((X14) = (k1_xboole_0))
% 0.82/1.03          | ((k2_zfmisc_1 @ X14 @ X13) != (k2_zfmisc_1 @ X15 @ X16))
% 0.82/1.03          | ((X14) = (X15)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.82/1.03  thf('26', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (((k2_zfmisc_1 @ X1 @ X0) != (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.82/1.03          | ((X1) = (k3_xboole_0 @ sk_A @ sk_A))
% 0.82/1.03          | ((X1) = (k1_xboole_0))
% 0.82/1.03          | ((X0) = (k1_xboole_0)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['24', '25'])).
% 0.82/1.03  thf('27', plain,
% 0.82/1.03      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.82/1.03        | ((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))
% 0.82/1.03        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 0.82/1.03        | ((k3_xboole_0 @ sk_C @ sk_A) = (k3_xboole_0 @ sk_A @ sk_A)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['15', '26'])).
% 0.82/1.03  thf('28', plain,
% 0.82/1.03      ((((k3_xboole_0 @ sk_C @ sk_A) = (k3_xboole_0 @ sk_A @ sk_A))
% 0.82/1.03        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 0.82/1.03        | ((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 0.82/1.03      inference('simplify', [status(thm)], ['27'])).
% 0.82/1.03  thf('29', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (((k2_zfmisc_1 @ X1 @ X0) != (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.82/1.03          | ((X1) = (k3_xboole_0 @ sk_A @ sk_A))
% 0.82/1.03          | ((X1) = (k1_xboole_0))
% 0.82/1.03          | ((X0) = (k1_xboole_0)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['24', '25'])).
% 0.82/1.03  thf('30', plain,
% 0.82/1.03      ((((sk_B) = (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k3_xboole_0 @ sk_A @ sk_A)))),
% 0.82/1.03      inference('eq_res', [status(thm)], ['29'])).
% 0.82/1.03  thf('31', plain,
% 0.82/1.03      ((((sk_A) = (k3_xboole_0 @ sk_C @ sk_A))
% 0.82/1.03        | ((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))
% 0.82/1.03        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k1_xboole_0))
% 0.82/1.03        | ((sk_B) = (k1_xboole_0)))),
% 0.82/1.03      inference('sup+', [status(thm)], ['28', '30'])).
% 0.82/1.03  thf('32', plain,
% 0.82/1.03      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.82/1.03         (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.82/1.03      inference('demod', [status(thm)], ['5', '6'])).
% 0.82/1.03  thf('33', plain,
% 0.82/1.03      ((((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ k1_xboole_0)
% 0.82/1.03          = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.82/1.03        | ((sk_B) = (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k1_xboole_0))
% 0.82/1.03        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k3_xboole_0 @ sk_C @ sk_A)))),
% 0.82/1.03      inference('sup+', [status(thm)], ['31', '32'])).
% 0.82/1.03  thf(t113_zfmisc_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.82/1.03       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.82/1.03  thf('34', plain,
% 0.82/1.03      (![X7 : $i, X8 : $i]:
% 0.82/1.03         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.82/1.03  thf('35', plain,
% 0.82/1.03      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.82/1.03      inference('simplify', [status(thm)], ['34'])).
% 0.82/1.03  thf('36', plain,
% 0.82/1.03      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.82/1.03        | ((sk_B) = (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k1_xboole_0))
% 0.82/1.03        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k3_xboole_0 @ sk_C @ sk_A)))),
% 0.82/1.03      inference('demod', [status(thm)], ['33', '35'])).
% 0.82/1.03  thf('37', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('38', plain,
% 0.82/1.03      ((((sk_B) = (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k1_xboole_0))
% 0.82/1.03        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k3_xboole_0 @ sk_C @ sk_A)))),
% 0.82/1.03      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.82/1.03  thf('39', plain,
% 0.82/1.03      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.82/1.03      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.82/1.03  thf('40', plain,
% 0.82/1.03      (((r1_tarski @ sk_A @ sk_C)
% 0.82/1.03        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k1_xboole_0))
% 0.82/1.03        | ((sk_B) = (k1_xboole_0)))),
% 0.82/1.03      inference('sup+', [status(thm)], ['38', '39'])).
% 0.82/1.03  thf('41', plain,
% 0.82/1.03      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.82/1.03         (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.82/1.03      inference('demod', [status(thm)], ['5', '6'])).
% 0.82/1.03  thf('42', plain,
% 0.82/1.03      ((((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_D @ sk_B))
% 0.82/1.03          = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.82/1.03        | ((sk_B) = (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k1_xboole_0))
% 0.82/1.03        | (r1_tarski @ sk_A @ sk_C))),
% 0.82/1.03      inference('sup+', [status(thm)], ['40', '41'])).
% 0.82/1.03  thf('43', plain,
% 0.82/1.03      (![X7 : $i, X8 : $i]:
% 0.82/1.03         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.82/1.03  thf('44', plain,
% 0.82/1.03      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.82/1.03      inference('simplify', [status(thm)], ['43'])).
% 0.82/1.03  thf('45', plain,
% 0.82/1.03      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.82/1.03        | ((sk_B) = (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k1_xboole_0))
% 0.82/1.03        | (r1_tarski @ sk_A @ sk_C))),
% 0.82/1.03      inference('demod', [status(thm)], ['42', '44'])).
% 0.82/1.03  thf('46', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('47', plain,
% 0.82/1.03      ((((sk_B) = (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k1_xboole_0))
% 0.82/1.03        | (r1_tarski @ sk_A @ sk_C))),
% 0.82/1.03      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.82/1.03  thf('48', plain,
% 0.82/1.03      ((~ (r1_tarski @ sk_A @ sk_C)) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.82/1.03      inference('split', [status(esa)], ['13'])).
% 0.82/1.03  thf('49', plain,
% 0.82/1.03      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.82/1.03         <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['47', '48'])).
% 0.82/1.03  thf('50', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('51', plain,
% 0.82/1.03      (((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))
% 0.82/1.03         | ((sk_A) = (k1_xboole_0)))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['49', '50'])).
% 0.82/1.03  thf('52', plain,
% 0.82/1.03      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.82/1.03      inference('simplify', [status(thm)], ['34'])).
% 0.82/1.03  thf('53', plain,
% 0.82/1.03      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.82/1.03         <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.82/1.03      inference('demod', [status(thm)], ['51', '52'])).
% 0.82/1.03  thf('54', plain,
% 0.82/1.03      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.82/1.03      inference('simplify', [status(thm)], ['53'])).
% 0.82/1.03  thf('55', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('56', plain,
% 0.82/1.03      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0)))
% 0.82/1.03         <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['54', '55'])).
% 0.82/1.03  thf('57', plain,
% 0.82/1.03      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.82/1.03      inference('simplify', [status(thm)], ['43'])).
% 0.82/1.03  thf('58', plain,
% 0.82/1.03      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.82/1.03      inference('demod', [status(thm)], ['56', '57'])).
% 0.82/1.03  thf('59', plain, (((r1_tarski @ sk_A @ sk_C))),
% 0.82/1.03      inference('simplify', [status(thm)], ['58'])).
% 0.82/1.03  thf('60', plain,
% 0.82/1.03      (~ ((r1_tarski @ sk_B @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C))),
% 0.82/1.03      inference('split', [status(esa)], ['13'])).
% 0.82/1.03  thf('61', plain, (~ ((r1_tarski @ sk_B @ sk_D))),
% 0.82/1.03      inference('sat_resolution*', [status(thm)], ['59', '60'])).
% 0.82/1.03  thf('62', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.82/1.03      inference('simpl_trail', [status(thm)], ['14', '61'])).
% 0.82/1.03  thf('63', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.82/1.03      inference('clc', [status(thm)], ['12', '62'])).
% 0.82/1.03  thf('64', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('65', plain,
% 0.82/1.03      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k1_xboole_0)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['63', '64'])).
% 0.82/1.03  thf('66', plain,
% 0.82/1.03      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.82/1.03      inference('simplify', [status(thm)], ['34'])).
% 0.82/1.03  thf('67', plain,
% 0.82/1.03      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.82/1.03      inference('demod', [status(thm)], ['65', '66'])).
% 0.82/1.03  thf('68', plain, (((sk_A) = (k1_xboole_0))),
% 0.82/1.03      inference('simplify', [status(thm)], ['67'])).
% 0.82/1.03  thf('69', plain,
% 0.82/1.03      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.82/1.03      inference('simplify', [status(thm)], ['43'])).
% 0.82/1.03  thf('70', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.82/1.03      inference('demod', [status(thm)], ['0', '68', '69'])).
% 0.82/1.03  thf('71', plain, ($false), inference('simplify', [status(thm)], ['70'])).
% 0.82/1.03  
% 0.82/1.03  % SZS output end Refutation
% 0.82/1.03  
% 0.82/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
