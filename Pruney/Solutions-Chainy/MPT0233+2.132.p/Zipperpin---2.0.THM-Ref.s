%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bX7tbLaQgM

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:51 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  140 (2557 expanded)
%              Number of leaves         :   24 ( 737 expanded)
%              Depth                    :   40
%              Number of atoms          : 1266 (27360 expanded)
%              Number of equality atoms :  212 (4181 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('0',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k1_tarski @ X26 ) @ ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X24
        = ( k2_tarski @ X22 @ X23 ) )
      | ( X24
        = ( k1_tarski @ X23 ) )
      | ( X24
        = ( k1_tarski @ X22 ) )
      | ( X24 = k1_xboole_0 )
      | ~ ( r1_tarski @ X24 @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('7',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t25_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X31 = X30 )
      | ( X31 = X32 )
      | ~ ( r1_tarski @ ( k1_tarski @ X31 ) @ ( k2_tarski @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ sk_D ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( X0 = sk_D )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_D )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('15',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ X24 @ ( k2_tarski @ X22 @ X25 ) )
      | ( X24
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('16',plain,(
    ! [X22: $i,X25: $i] :
      ( r1_tarski @ ( k1_tarski @ X25 ) @ ( k2_tarski @ X22 @ X25 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X31 = X30 )
      | ( X31 = X32 )
      | ~ ( r1_tarski @ ( k1_tarski @ X31 ) @ ( k2_tarski @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('19',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_B )
    | ( sk_D = sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf(t9_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ B @ C ) )
     => ( B = C ) ) )).

thf('22',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X34 = X33 )
      | ( ( k1_tarski @ X35 )
       != ( k2_tarski @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t9_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_D ) )
      | ( sk_D = sk_B )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_B ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('25',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X34 = X33 )
      | ( ( k1_tarski @ X35 )
       != ( k2_tarski @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t9_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_C ) )
      | ( sk_D = sk_B )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_D = sk_B )
      | ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_D = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('29',plain,(
    ! [X22: $i,X25: $i] :
      ( r1_tarski @ ( k1_tarski @ X25 ) @ ( k2_tarski @ X22 @ X25 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('30',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( sk_A = sk_B )
    | ( sk_D = sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('31',plain,(
    ! [X8: $i] :
      ( ( r1_xboole_0 @ X8 @ X8 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('32',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_xboole_0 @ X15 @ ( k4_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X10 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X10 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_D = sk_B )
    | ( sk_A = sk_B )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','55'])).

thf('57',plain,
    ( ( sk_D = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('58',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X34 = X33 )
      | ( ( k1_tarski @ X35 )
       != ( k2_tarski @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t9_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( sk_A = sk_B )
      | ( sk_D = sk_B )
      | ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( sk_D = sk_B )
      | ( sk_A = sk_B )
      | ( ( k1_tarski @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( sk_A = sk_B )
    | ( sk_D = sk_B ) ),
    inference(clc,[status(thm)],['56','60'])).

thf('62',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11','12'])).

thf('63',plain,
    ( ( ( k2_tarski @ sk_A @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( sk_A = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X34 = X33 )
      | ( ( k1_tarski @ X35 )
       != ( k2_tarski @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t9_zfmisc_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = sk_B )
      | ( ( k2_tarski @ sk_A @ sk_D )
        = ( k1_tarski @ sk_D ) )
      | ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_D )
        = ( k1_tarski @ sk_D ) )
      | ( sk_A = sk_B )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_D )
      = ( k1_tarski @ sk_D ) ) ),
    inference(eq_res,[status(thm)],['66'])).

thf('68',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k1_tarski @ X26 ) @ ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('69',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( ( k2_tarski @ sk_A @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( sk_A = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('73',plain,
    ( ( ( k2_tarski @ sk_A @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( sk_A = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X34 = X33 )
      | ( ( k1_tarski @ X35 )
       != ( k2_tarski @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t9_zfmisc_1])).

thf('75',plain,
    ( ( sk_A = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_D )
      = ( k1_tarski @ sk_D ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X34 = X33 )
      | ( ( k1_tarski @ X35 )
       != ( k2_tarski @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t9_zfmisc_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_D ) )
      | ( sk_A = sk_B )
      | ( sk_A = sk_D ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_D ) )
      | ( sk_A = sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A = sk_B ),
    inference(eq_res,[status(thm)],['79'])).

thf('81',plain,(
    sk_A = sk_B ),
    inference(eq_res,[status(thm)],['79'])).

thf('82',plain,(
    sk_A = sk_B ),
    inference(eq_res,[status(thm)],['79'])).

thf('83',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_A )
      = ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['13','80','81','82'])).

thf('84',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X31 = X30 )
      | ( X31 = X32 )
      | ~ ( r1_tarski @ ( k1_tarski @ X31 ) @ ( k2_tarski @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_D ) )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( X0 = sk_A )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = ( k1_tarski @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_D = sk_A ) ),
    inference('sup-',[status(thm)],['3','86'])).

thf('88',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X31 = X30 )
      | ( X31 = X32 )
      | ~ ( r1_tarski @ ( k1_tarski @ X31 ) @ ( k2_tarski @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( X0 = sk_A )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_C = sk_A ) ),
    inference('sup-',[status(thm)],['2','92'])).

thf('94',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k2_tarski @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('97',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( ( k2_tarski @ sk_A @ sk_A )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('99',plain,
    ( ( k2_tarski @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('100',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf(t18_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf('101',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X29 = X28 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X29 ) @ ( k1_tarski @ X28 ) )
       != ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t18_zfmisc_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
       != ( k1_tarski @ sk_A ) )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('104',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('105',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['102','109','110'])).

thf('112',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','112'])).

thf('114',plain,(
    $false ),
    inference(simplify,[status(thm)],['113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bX7tbLaQgM
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.34/1.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.34/1.56  % Solved by: fo/fo7.sh
% 1.34/1.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.34/1.56  % done 857 iterations in 1.106s
% 1.34/1.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.34/1.56  % SZS output start Refutation
% 1.34/1.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.34/1.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.34/1.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.34/1.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.34/1.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.34/1.56  thf(sk_D_type, type, sk_D: $i).
% 1.34/1.56  thf(sk_C_type, type, sk_C: $i).
% 1.34/1.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.34/1.56  thf(sk_A_type, type, sk_A: $i).
% 1.34/1.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.34/1.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.34/1.56  thf(sk_B_type, type, sk_B: $i).
% 1.34/1.56  thf(t28_zfmisc_1, conjecture,
% 1.34/1.56    (![A:$i,B:$i,C:$i,D:$i]:
% 1.34/1.56     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 1.34/1.56          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 1.34/1.56  thf(zf_stmt_0, negated_conjecture,
% 1.34/1.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.34/1.56        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 1.34/1.56             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 1.34/1.56    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 1.34/1.56  thf('0', plain, (((sk_A) != (sk_D))),
% 1.34/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.56  thf(d10_xboole_0, axiom,
% 1.34/1.56    (![A:$i,B:$i]:
% 1.34/1.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.34/1.56  thf('1', plain,
% 1.34/1.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.34/1.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.34/1.56  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.34/1.56      inference('simplify', [status(thm)], ['1'])).
% 1.34/1.56  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.34/1.56      inference('simplify', [status(thm)], ['1'])).
% 1.34/1.56  thf(t12_zfmisc_1, axiom,
% 1.34/1.56    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 1.34/1.56  thf('4', plain,
% 1.34/1.56      (![X26 : $i, X27 : $i]:
% 1.34/1.56         (r1_tarski @ (k1_tarski @ X26) @ (k2_tarski @ X26 @ X27))),
% 1.34/1.56      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 1.34/1.56  thf('5', plain,
% 1.34/1.56      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 1.34/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.56  thf(l45_zfmisc_1, axiom,
% 1.34/1.56    (![A:$i,B:$i,C:$i]:
% 1.34/1.56     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 1.34/1.56       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 1.34/1.56            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 1.34/1.56  thf('6', plain,
% 1.34/1.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.34/1.56         (((X24) = (k2_tarski @ X22 @ X23))
% 1.34/1.56          | ((X24) = (k1_tarski @ X23))
% 1.34/1.56          | ((X24) = (k1_tarski @ X22))
% 1.34/1.56          | ((X24) = (k1_xboole_0))
% 1.34/1.56          | ~ (r1_tarski @ X24 @ (k2_tarski @ X22 @ X23)))),
% 1.34/1.56      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 1.34/1.56  thf('7', plain,
% 1.34/1.56      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['5', '6'])).
% 1.34/1.56  thf(t25_zfmisc_1, axiom,
% 1.34/1.56    (![A:$i,B:$i,C:$i]:
% 1.34/1.56     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 1.34/1.56          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 1.34/1.56  thf('8', plain,
% 1.34/1.56      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.34/1.56         (((X31) = (X30))
% 1.34/1.56          | ((X31) = (X32))
% 1.34/1.56          | ~ (r1_tarski @ (k1_tarski @ X31) @ (k2_tarski @ X30 @ X32)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 1.34/1.56  thf('9', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (~ (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ sk_A @ sk_B))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56          | ((X0) = (sk_D))
% 1.34/1.56          | ((X0) = (sk_C)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['7', '8'])).
% 1.34/1.56  thf('10', plain,
% 1.34/1.56      ((((sk_A) = (sk_C))
% 1.34/1.56        | ((sk_A) = (sk_D))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['4', '9'])).
% 1.34/1.56  thf('11', plain, (((sk_A) != (sk_D))),
% 1.34/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.56  thf('12', plain, (((sk_A) != (sk_C))),
% 1.34/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.56  thf('13', plain,
% 1.34/1.56      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D)))),
% 1.34/1.56      inference('simplify_reflect-', [status(thm)], ['10', '11', '12'])).
% 1.34/1.56  thf('14', plain,
% 1.34/1.56      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['5', '6'])).
% 1.34/1.56  thf('15', plain,
% 1.34/1.56      (![X22 : $i, X24 : $i, X25 : $i]:
% 1.34/1.56         ((r1_tarski @ X24 @ (k2_tarski @ X22 @ X25))
% 1.34/1.56          | ((X24) != (k1_tarski @ X25)))),
% 1.34/1.56      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 1.34/1.56  thf('16', plain,
% 1.34/1.56      (![X22 : $i, X25 : $i]:
% 1.34/1.56         (r1_tarski @ (k1_tarski @ X25) @ (k2_tarski @ X22 @ X25))),
% 1.34/1.56      inference('simplify', [status(thm)], ['15'])).
% 1.34/1.56  thf('17', plain,
% 1.34/1.56      (((r1_tarski @ (k1_tarski @ sk_D) @ (k2_tarski @ sk_A @ sk_B))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.34/1.56      inference('sup+', [status(thm)], ['14', '16'])).
% 1.34/1.56  thf('18', plain,
% 1.34/1.56      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.34/1.56         (((X31) = (X30))
% 1.34/1.56          | ((X31) = (X32))
% 1.34/1.56          | ~ (r1_tarski @ (k1_tarski @ X31) @ (k2_tarski @ X30 @ X32)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 1.34/1.56  thf('19', plain,
% 1.34/1.56      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 1.34/1.56        | ((sk_D) = (sk_B))
% 1.34/1.56        | ((sk_D) = (sk_A)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['17', '18'])).
% 1.34/1.56  thf('20', plain, (((sk_A) != (sk_D))),
% 1.34/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.56  thf('21', plain,
% 1.34/1.56      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 1.34/1.56        | ((sk_D) = (sk_B)))),
% 1.34/1.56      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 1.34/1.56  thf(t9_zfmisc_1, axiom,
% 1.34/1.56    (![A:$i,B:$i,C:$i]:
% 1.34/1.56     ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( B ) = ( C ) ) ))).
% 1.34/1.56  thf('22', plain,
% 1.34/1.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.34/1.56         (((X34) = (X33)) | ((k1_tarski @ X35) != (k2_tarski @ X34 @ X33)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t9_zfmisc_1])).
% 1.34/1.56  thf('23', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (((k1_tarski @ X0) != (k1_tarski @ sk_D))
% 1.34/1.56          | ((sk_D) = (sk_B))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56          | ((sk_A) = (sk_B)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['21', '22'])).
% 1.34/1.56  thf('24', plain,
% 1.34/1.56      ((((sk_A) = (sk_B))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 1.34/1.56        | ((sk_D) = (sk_B)))),
% 1.34/1.56      inference('eq_res', [status(thm)], ['23'])).
% 1.34/1.56  thf('25', plain,
% 1.34/1.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.34/1.56         (((X34) = (X33)) | ((k1_tarski @ X35) != (k2_tarski @ X34 @ X33)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t9_zfmisc_1])).
% 1.34/1.56  thf('26', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (((k1_tarski @ X0) != (k1_tarski @ sk_C))
% 1.34/1.56          | ((sk_D) = (sk_B))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56          | ((sk_A) = (sk_B))
% 1.34/1.56          | ((sk_A) = (sk_B)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['24', '25'])).
% 1.34/1.56  thf('27', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (((sk_A) = (sk_B))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56          | ((sk_D) = (sk_B))
% 1.34/1.56          | ((k1_tarski @ X0) != (k1_tarski @ sk_C)))),
% 1.34/1.56      inference('simplify', [status(thm)], ['26'])).
% 1.34/1.56  thf('28', plain,
% 1.34/1.56      ((((sk_D) = (sk_B))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56        | ((sk_A) = (sk_B)))),
% 1.34/1.56      inference('eq_res', [status(thm)], ['27'])).
% 1.34/1.56  thf('29', plain,
% 1.34/1.56      (![X22 : $i, X25 : $i]:
% 1.34/1.56         (r1_tarski @ (k1_tarski @ X25) @ (k2_tarski @ X22 @ X25))),
% 1.34/1.56      inference('simplify', [status(thm)], ['15'])).
% 1.34/1.56  thf('30', plain,
% 1.34/1.56      (((r1_tarski @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 1.34/1.56        | ((sk_A) = (sk_B))
% 1.34/1.56        | ((sk_D) = (sk_B)))),
% 1.34/1.56      inference('sup+', [status(thm)], ['28', '29'])).
% 1.34/1.56  thf(t66_xboole_1, axiom,
% 1.34/1.56    (![A:$i]:
% 1.34/1.56     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 1.34/1.56       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.34/1.56  thf('31', plain,
% 1.34/1.56      (![X8 : $i]: ((r1_xboole_0 @ X8 @ X8) | ((X8) != (k1_xboole_0)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t66_xboole_1])).
% 1.34/1.56  thf('32', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 1.34/1.56      inference('simplify', [status(thm)], ['31'])).
% 1.34/1.56  thf('33', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.34/1.56      inference('simplify', [status(thm)], ['1'])).
% 1.34/1.56  thf(l32_xboole_1, axiom,
% 1.34/1.56    (![A:$i,B:$i]:
% 1.34/1.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.34/1.56  thf('34', plain,
% 1.34/1.56      (![X3 : $i, X5 : $i]:
% 1.34/1.56         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 1.34/1.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.34/1.56  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.34/1.56      inference('sup-', [status(thm)], ['33', '34'])).
% 1.34/1.56  thf(t81_xboole_1, axiom,
% 1.34/1.56    (![A:$i,B:$i,C:$i]:
% 1.34/1.56     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.34/1.56       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.34/1.56  thf('36', plain,
% 1.34/1.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.34/1.56         ((r1_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 1.34/1.56          | ~ (r1_xboole_0 @ X15 @ (k4_xboole_0 @ X14 @ X16)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t81_xboole_1])).
% 1.34/1.56  thf('37', plain,
% 1.34/1.56      (![X0 : $i, X1 : $i]:
% 1.34/1.56         (~ (r1_xboole_0 @ X1 @ k1_xboole_0)
% 1.34/1.56          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['35', '36'])).
% 1.34/1.56  thf('38', plain,
% 1.34/1.56      (![X0 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.34/1.56      inference('sup-', [status(thm)], ['32', '37'])).
% 1.34/1.56  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.34/1.56      inference('sup-', [status(thm)], ['33', '34'])).
% 1.34/1.56  thf(t51_xboole_1, axiom,
% 1.34/1.56    (![A:$i,B:$i]:
% 1.34/1.56     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.34/1.56       ( A ) ))).
% 1.34/1.56  thf('40', plain,
% 1.34/1.56      (![X6 : $i, X7 : $i]:
% 1.34/1.56         ((k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X7))
% 1.34/1.56           = (X6))),
% 1.34/1.56      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.34/1.56  thf('41', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0) = (X0))),
% 1.34/1.56      inference('sup+', [status(thm)], ['39', '40'])).
% 1.34/1.56  thf(t70_xboole_1, axiom,
% 1.34/1.56    (![A:$i,B:$i,C:$i]:
% 1.34/1.56     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.34/1.56            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.34/1.56       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.34/1.56            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.34/1.56  thf('42', plain,
% 1.34/1.56      (![X10 : $i, X11 : $i, X13 : $i]:
% 1.34/1.56         ((r1_xboole_0 @ X10 @ X13)
% 1.34/1.56          | ~ (r1_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X13)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.34/1.56  thf('43', plain,
% 1.34/1.56      (![X0 : $i, X1 : $i]:
% 1.34/1.56         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 1.34/1.56      inference('sup-', [status(thm)], ['41', '42'])).
% 1.34/1.56  thf('44', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.34/1.56      inference('sup-', [status(thm)], ['38', '43'])).
% 1.34/1.56  thf('45', plain,
% 1.34/1.56      (![X6 : $i, X7 : $i]:
% 1.34/1.56         ((k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X7))
% 1.34/1.56           = (X6))),
% 1.34/1.56      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.34/1.56  thf('46', plain,
% 1.34/1.56      (![X10 : $i, X11 : $i, X13 : $i]:
% 1.34/1.56         ((r1_xboole_0 @ X10 @ X13)
% 1.34/1.56          | ~ (r1_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X13)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.34/1.56  thf('47', plain,
% 1.34/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.56         (~ (r1_xboole_0 @ X2 @ X0)
% 1.34/1.56          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['45', '46'])).
% 1.34/1.56  thf('48', plain,
% 1.34/1.56      (![X0 : $i, X1 : $i]:
% 1.34/1.56         (r1_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))),
% 1.34/1.56      inference('sup-', [status(thm)], ['44', '47'])).
% 1.34/1.56  thf('49', plain,
% 1.34/1.56      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X9 @ X9))),
% 1.34/1.56      inference('cnf', [status(esa)], [t66_xboole_1])).
% 1.34/1.56  thf('50', plain,
% 1.34/1.56      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.34/1.56      inference('sup-', [status(thm)], ['48', '49'])).
% 1.34/1.56  thf('51', plain,
% 1.34/1.56      (![X3 : $i, X4 : $i]:
% 1.34/1.56         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 1.34/1.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.34/1.56  thf('52', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 1.34/1.56      inference('sup-', [status(thm)], ['50', '51'])).
% 1.34/1.56  thf('53', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.34/1.56      inference('simplify', [status(thm)], ['52'])).
% 1.34/1.56  thf('54', plain,
% 1.34/1.56      (![X0 : $i, X2 : $i]:
% 1.34/1.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.34/1.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.34/1.56  thf('55', plain,
% 1.34/1.56      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['53', '54'])).
% 1.34/1.56  thf('56', plain,
% 1.34/1.56      ((((sk_D) = (sk_B))
% 1.34/1.56        | ((sk_A) = (sk_B))
% 1.34/1.56        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['30', '55'])).
% 1.34/1.56  thf('57', plain,
% 1.34/1.56      ((((sk_D) = (sk_B))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56        | ((sk_A) = (sk_B)))),
% 1.34/1.56      inference('eq_res', [status(thm)], ['27'])).
% 1.34/1.56  thf('58', plain,
% 1.34/1.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.34/1.56         (((X34) = (X33)) | ((k1_tarski @ X35) != (k2_tarski @ X34 @ X33)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t9_zfmisc_1])).
% 1.34/1.56  thf('59', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (((k1_tarski @ X0) != (k1_xboole_0))
% 1.34/1.56          | ((sk_A) = (sk_B))
% 1.34/1.56          | ((sk_D) = (sk_B))
% 1.34/1.56          | ((sk_A) = (sk_B)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['57', '58'])).
% 1.34/1.56  thf('60', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (((sk_D) = (sk_B))
% 1.34/1.56          | ((sk_A) = (sk_B))
% 1.34/1.56          | ((k1_tarski @ X0) != (k1_xboole_0)))),
% 1.34/1.56      inference('simplify', [status(thm)], ['59'])).
% 1.34/1.56  thf('61', plain, ((((sk_A) = (sk_B)) | ((sk_D) = (sk_B)))),
% 1.34/1.56      inference('clc', [status(thm)], ['56', '60'])).
% 1.34/1.56  thf('62', plain,
% 1.34/1.56      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D)))),
% 1.34/1.56      inference('simplify_reflect-', [status(thm)], ['10', '11', '12'])).
% 1.34/1.56  thf('63', plain,
% 1.34/1.56      ((((k2_tarski @ sk_A @ sk_D) = (k1_tarski @ sk_D))
% 1.34/1.56        | ((sk_A) = (sk_B))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.34/1.56      inference('sup+', [status(thm)], ['61', '62'])).
% 1.34/1.56  thf('64', plain,
% 1.34/1.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.34/1.56         (((X34) = (X33)) | ((k1_tarski @ X35) != (k2_tarski @ X34 @ X33)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t9_zfmisc_1])).
% 1.34/1.56  thf('65', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (((k1_tarski @ X0) != (k1_tarski @ sk_C))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56          | ((sk_A) = (sk_B))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_D) = (k1_tarski @ sk_D))
% 1.34/1.56          | ((sk_A) = (sk_B)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['63', '64'])).
% 1.34/1.56  thf('66', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (((k2_tarski @ sk_A @ sk_D) = (k1_tarski @ sk_D))
% 1.34/1.56          | ((sk_A) = (sk_B))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56          | ((k1_tarski @ X0) != (k1_tarski @ sk_C)))),
% 1.34/1.56      inference('simplify', [status(thm)], ['65'])).
% 1.34/1.56  thf('67', plain,
% 1.34/1.56      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 1.34/1.56        | ((sk_A) = (sk_B))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_D) = (k1_tarski @ sk_D)))),
% 1.34/1.56      inference('eq_res', [status(thm)], ['66'])).
% 1.34/1.56  thf('68', plain,
% 1.34/1.56      (![X26 : $i, X27 : $i]:
% 1.34/1.56         (r1_tarski @ (k1_tarski @ X26) @ (k2_tarski @ X26 @ X27))),
% 1.34/1.56      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 1.34/1.56  thf('69', plain,
% 1.34/1.56      (![X0 : $i, X2 : $i]:
% 1.34/1.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.34/1.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.34/1.56  thf('70', plain,
% 1.34/1.56      (![X0 : $i, X1 : $i]:
% 1.34/1.56         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 1.34/1.56          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['68', '69'])).
% 1.34/1.56  thf('71', plain,
% 1.34/1.56      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_A))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_D) = (k1_tarski @ sk_D))
% 1.34/1.56        | ((sk_A) = (sk_B))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_A)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['67', '70'])).
% 1.34/1.56  thf('72', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.34/1.56      inference('simplify', [status(thm)], ['52'])).
% 1.34/1.56  thf('73', plain,
% 1.34/1.56      ((((k2_tarski @ sk_A @ sk_D) = (k1_tarski @ sk_D))
% 1.34/1.56        | ((sk_A) = (sk_B))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_A)))),
% 1.34/1.56      inference('demod', [status(thm)], ['71', '72'])).
% 1.34/1.56  thf('74', plain,
% 1.34/1.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.34/1.56         (((X34) = (X33)) | ((k1_tarski @ X35) != (k2_tarski @ X34 @ X33)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t9_zfmisc_1])).
% 1.34/1.56  thf('75', plain,
% 1.34/1.56      ((((sk_A) = (sk_B)) | ((k2_tarski @ sk_A @ sk_D) = (k1_tarski @ sk_D)))),
% 1.34/1.56      inference('clc', [status(thm)], ['73', '74'])).
% 1.34/1.56  thf('76', plain,
% 1.34/1.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.34/1.56         (((X34) = (X33)) | ((k1_tarski @ X35) != (k2_tarski @ X34 @ X33)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t9_zfmisc_1])).
% 1.34/1.56  thf('77', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (((k1_tarski @ X0) != (k1_tarski @ sk_D))
% 1.34/1.56          | ((sk_A) = (sk_B))
% 1.34/1.56          | ((sk_A) = (sk_D)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['75', '76'])).
% 1.34/1.56  thf('78', plain, (((sk_A) != (sk_D))),
% 1.34/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.56  thf('79', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (((k1_tarski @ X0) != (k1_tarski @ sk_D)) | ((sk_A) = (sk_B)))),
% 1.34/1.56      inference('simplify_reflect-', [status(thm)], ['77', '78'])).
% 1.34/1.56  thf('80', plain, (((sk_A) = (sk_B))),
% 1.34/1.56      inference('eq_res', [status(thm)], ['79'])).
% 1.34/1.56  thf('81', plain, (((sk_A) = (sk_B))),
% 1.34/1.56      inference('eq_res', [status(thm)], ['79'])).
% 1.34/1.56  thf('82', plain, (((sk_A) = (sk_B))),
% 1.34/1.56      inference('eq_res', [status(thm)], ['79'])).
% 1.34/1.56  thf('83', plain,
% 1.34/1.56      ((((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_C))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_D)))),
% 1.34/1.56      inference('demod', [status(thm)], ['13', '80', '81', '82'])).
% 1.34/1.56  thf('84', plain,
% 1.34/1.56      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.34/1.56         (((X31) = (X30))
% 1.34/1.56          | ((X31) = (X32))
% 1.34/1.56          | ~ (r1_tarski @ (k1_tarski @ X31) @ (k2_tarski @ X30 @ X32)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 1.34/1.56  thf('85', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ sk_D))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_C))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 1.34/1.56          | ((X0) = (sk_A))
% 1.34/1.56          | ((X0) = (sk_A)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['83', '84'])).
% 1.34/1.56  thf('86', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (((X0) = (sk_A))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_C))
% 1.34/1.56          | ~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ sk_D)))),
% 1.34/1.56      inference('simplify', [status(thm)], ['85'])).
% 1.34/1.56  thf('87', plain,
% 1.34/1.56      ((((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_C))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 1.34/1.56        | ((sk_D) = (sk_A)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['3', '86'])).
% 1.34/1.56  thf('88', plain, (((sk_A) != (sk_D))),
% 1.34/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.56  thf('89', plain,
% 1.34/1.56      ((((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_C))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0)))),
% 1.34/1.56      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 1.34/1.56  thf('90', plain,
% 1.34/1.56      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.34/1.56         (((X31) = (X30))
% 1.34/1.56          | ((X31) = (X32))
% 1.34/1.56          | ~ (r1_tarski @ (k1_tarski @ X31) @ (k2_tarski @ X30 @ X32)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 1.34/1.56  thf('91', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ sk_C))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 1.34/1.56          | ((X0) = (sk_A))
% 1.34/1.56          | ((X0) = (sk_A)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['89', '90'])).
% 1.34/1.56  thf('92', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (((X0) = (sk_A))
% 1.34/1.56          | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 1.34/1.56          | ~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ sk_C)))),
% 1.34/1.56      inference('simplify', [status(thm)], ['91'])).
% 1.34/1.56  thf('93', plain,
% 1.34/1.56      ((((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_A)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['2', '92'])).
% 1.34/1.56  thf('94', plain, (((sk_A) != (sk_C))),
% 1.34/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.56  thf('95', plain, (((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))),
% 1.34/1.56      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 1.34/1.56  thf('96', plain,
% 1.34/1.56      (![X0 : $i, X1 : $i]:
% 1.34/1.56         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 1.34/1.56          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['68', '69'])).
% 1.34/1.56  thf('97', plain,
% 1.34/1.56      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_A))
% 1.34/1.56        | ((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_A)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['95', '96'])).
% 1.34/1.56  thf('98', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.34/1.56      inference('simplify', [status(thm)], ['52'])).
% 1.34/1.56  thf('99', plain, (((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))),
% 1.34/1.56      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 1.34/1.56  thf('100', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 1.34/1.56      inference('demod', [status(thm)], ['97', '98', '99'])).
% 1.34/1.56  thf(t18_zfmisc_1, axiom,
% 1.34/1.56    (![A:$i,B:$i]:
% 1.34/1.56     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.34/1.56         ( k1_tarski @ A ) ) =>
% 1.34/1.56       ( ( A ) = ( B ) ) ))).
% 1.34/1.56  thf('101', plain,
% 1.34/1.56      (![X28 : $i, X29 : $i]:
% 1.34/1.56         (((X29) = (X28))
% 1.34/1.56          | ((k3_xboole_0 @ (k1_tarski @ X29) @ (k1_tarski @ X28))
% 1.34/1.56              != (k1_tarski @ X29)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t18_zfmisc_1])).
% 1.34/1.56  thf('102', plain,
% 1.34/1.56      (![X0 : $i]:
% 1.34/1.56         (((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) != (k1_tarski @ sk_A))
% 1.34/1.56          | ((sk_A) = (X0)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['100', '101'])).
% 1.34/1.56  thf('103', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.34/1.56      inference('sup-', [status(thm)], ['38', '43'])).
% 1.34/1.56  thf('104', plain,
% 1.34/1.56      (![X6 : $i, X7 : $i]:
% 1.34/1.56         ((k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X7))
% 1.34/1.56           = (X6))),
% 1.34/1.56      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.34/1.56  thf('105', plain,
% 1.34/1.56      (![X10 : $i, X11 : $i, X13 : $i]:
% 1.34/1.56         ((r1_xboole_0 @ X10 @ X11)
% 1.34/1.56          | ~ (r1_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X13)))),
% 1.34/1.56      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.34/1.56  thf('106', plain,
% 1.34/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.56         (~ (r1_xboole_0 @ X2 @ X0)
% 1.34/1.56          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.34/1.56      inference('sup-', [status(thm)], ['104', '105'])).
% 1.34/1.56  thf('107', plain,
% 1.34/1.56      (![X0 : $i, X1 : $i]:
% 1.34/1.56         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X1))),
% 1.34/1.56      inference('sup-', [status(thm)], ['103', '106'])).
% 1.34/1.56  thf('108', plain,
% 1.34/1.56      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X9 @ X9))),
% 1.34/1.56      inference('cnf', [status(esa)], [t66_xboole_1])).
% 1.34/1.56  thf('109', plain,
% 1.34/1.56      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.34/1.56      inference('sup-', [status(thm)], ['107', '108'])).
% 1.34/1.56  thf('110', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 1.34/1.56      inference('demod', [status(thm)], ['97', '98', '99'])).
% 1.34/1.56  thf('111', plain,
% 1.34/1.56      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (X0)))),
% 1.34/1.56      inference('demod', [status(thm)], ['102', '109', '110'])).
% 1.34/1.56  thf('112', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 1.34/1.56      inference('simplify', [status(thm)], ['111'])).
% 1.34/1.56  thf('113', plain, (((sk_A) != (sk_A))),
% 1.34/1.56      inference('demod', [status(thm)], ['0', '112'])).
% 1.34/1.56  thf('114', plain, ($false), inference('simplify', [status(thm)], ['113'])).
% 1.34/1.56  
% 1.34/1.56  % SZS output end Refutation
% 1.34/1.56  
% 1.34/1.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
