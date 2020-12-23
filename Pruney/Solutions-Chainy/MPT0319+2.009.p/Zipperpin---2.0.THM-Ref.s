%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XZE1Lm7xCO

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:31 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 166 expanded)
%              Number of leaves         :   24 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  696 (1469 expanded)
%              Number of equality atoms :   63 ( 130 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('0',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X33 ) )
        = ( k1_tarski @ X32 ) )
      | ( X32 = X33 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ X15 )
      | ( ( k4_xboole_0 @ X13 @ X15 )
       != X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X23 @ X25 ) @ ( k3_xboole_0 @ X24 @ X26 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( X1 = X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ ( k1_tarski @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('10',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ( ( k2_zfmisc_1 @ X30 @ ( k4_xboole_0 @ X27 @ X29 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X30 @ X27 ) @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['13','18'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','23'])).

thf('25',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X23 @ X25 ) @ ( k3_xboole_0 @ X24 @ X26 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('26',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('28',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X1 = X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ ( k1_tarski @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['9','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ ( k1_tarski @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ ( k1_tarski @ X0 ) ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t131_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( A != B )
     => ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) )
        & ( r1_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( A != B )
       => ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) )
          & ( r1_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t131_zfmisc_1])).

thf('31',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( sk_A = sk_B )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( $false
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( X3 = X2 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X3 ) @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X27 @ X29 ) @ X28 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X23 @ X25 ) @ ( k3_xboole_0 @ X24 @ X26 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('44',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X3 = X2 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X3 ) @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X3 ) @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) )
      | ( X3 = X2 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference(split,[status(esa)],['31'])).

thf('49',plain,
    ( ( sk_A = sk_B )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference(split,[status(esa)],['31'])).

thf('53',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['35','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XZE1Lm7xCO
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:15:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.76/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.99  % Solved by: fo/fo7.sh
% 0.76/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.99  % done 438 iterations in 0.532s
% 0.76/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.99  % SZS output start Refutation
% 0.76/0.99  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.76/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.99  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.76/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.99  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.76/0.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.99  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.99  thf(sk_D_type, type, sk_D: $i).
% 0.76/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.99  thf(t20_zfmisc_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.76/0.99         ( k1_tarski @ A ) ) <=>
% 0.76/0.99       ( ( A ) != ( B ) ) ))).
% 0.76/0.99  thf('0', plain,
% 0.76/0.99      (![X32 : $i, X33 : $i]:
% 0.76/0.99         (((k4_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X33))
% 0.76/0.99            = (k1_tarski @ X32))
% 0.76/0.99          | ((X32) = (X33)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.76/0.99  thf(t83_xboole_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.76/0.99  thf('1', plain,
% 0.76/0.99      (![X13 : $i, X15 : $i]:
% 0.76/0.99         ((r1_xboole_0 @ X13 @ X15) | ((k4_xboole_0 @ X13 @ X15) != (X13)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.76/0.99  thf('2', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.76/0.99          | ((X0) = (X1))
% 0.76/0.99          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.99  thf('3', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.76/0.99      inference('simplify', [status(thm)], ['2'])).
% 0.76/0.99  thf(d7_xboole_0, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.76/0.99       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.76/0.99  thf('4', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.76/0.99      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/0.99  thf('5', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         (((X1) = (X0))
% 0.76/0.99          | ((k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.76/0.99              = (k1_xboole_0)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.99  thf(t123_zfmisc_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.99     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.76/0.99       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.76/0.99  thf('6', plain,
% 0.76/0.99      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.76/0.99         ((k2_zfmisc_1 @ (k3_xboole_0 @ X23 @ X25) @ (k3_xboole_0 @ X24 @ X26))
% 0.76/0.99           = (k3_xboole_0 @ (k2_zfmisc_1 @ X23 @ X24) @ 
% 0.76/0.99              (k2_zfmisc_1 @ X25 @ X26)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.76/0.99  thf('7', plain,
% 0.76/0.99      (![X0 : $i, X2 : $i]:
% 0.76/0.99         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.76/0.99      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/0.99  thf('8', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.99         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.99            != (k1_xboole_0))
% 0.76/0.99          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/0.99  thf('9', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.99         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ k1_xboole_0)
% 0.76/0.99            != (k1_xboole_0))
% 0.76/0.99          | ((X1) = (X0))
% 0.76/0.99          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ (k1_tarski @ X1)) @ 
% 0.76/0.99             (k2_zfmisc_1 @ X2 @ (k1_tarski @ X0))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['5', '8'])).
% 0.76/0.99  thf(t125_zfmisc_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.76/0.99         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.76/0.99       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.76/0.99         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.76/0.99  thf('10', plain,
% 0.76/0.99      (![X27 : $i, X29 : $i, X30 : $i]:
% 0.76/0.99         ((k2_zfmisc_1 @ X30 @ (k4_xboole_0 @ X27 @ X29))
% 0.76/0.99           = (k4_xboole_0 @ (k2_zfmisc_1 @ X30 @ X27) @ 
% 0.76/0.99              (k2_zfmisc_1 @ X30 @ X29)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.76/0.99  thf(t3_boole, axiom,
% 0.76/0.99    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.76/0.99  thf('11', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.76/0.99      inference('cnf', [status(esa)], [t3_boole])).
% 0.76/0.99  thf(t96_xboole_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.76/0.99  thf('12', plain,
% 0.76/0.99      (![X18 : $i, X19 : $i]:
% 0.76/0.99         (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ (k5_xboole_0 @ X18 @ X19))),
% 0.76/0.99      inference('cnf', [status(esa)], [t96_xboole_1])).
% 0.76/0.99  thf('13', plain,
% 0.76/0.99      (![X0 : $i]: (r1_tarski @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/0.99      inference('sup+', [status(thm)], ['11', '12'])).
% 0.76/0.99  thf(t2_boole, axiom,
% 0.76/0.99    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.76/0.99  thf('14', plain,
% 0.76/0.99      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.99      inference('cnf', [status(esa)], [t2_boole])).
% 0.76/0.99  thf(t100_xboole_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.76/0.99  thf('15', plain,
% 0.76/0.99      (![X6 : $i, X7 : $i]:
% 0.76/0.99         ((k4_xboole_0 @ X6 @ X7)
% 0.76/0.99           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/0.99  thf('16', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/0.99      inference('sup+', [status(thm)], ['14', '15'])).
% 0.76/0.99  thf('17', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.76/0.99      inference('cnf', [status(esa)], [t3_boole])).
% 0.76/0.99  thf('18', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/0.99      inference('sup+', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('19', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.76/0.99      inference('demod', [status(thm)], ['13', '18'])).
% 0.76/0.99  thf(t106_xboole_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.76/0.99       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.76/0.99  thf('20', plain,
% 0.76/0.99      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.76/0.99         ((r1_xboole_0 @ X8 @ X10)
% 0.76/0.99          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.76/0.99  thf('21', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.76/0.99      inference('sup-', [status(thm)], ['19', '20'])).
% 0.76/0.99  thf('22', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.76/0.99      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/0.99  thf('23', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.99  thf('24', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.99         ((k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.76/0.99           (k2_zfmisc_1 @ X2 @ X0)) = (k1_xboole_0))),
% 0.76/0.99      inference('sup+', [status(thm)], ['10', '23'])).
% 0.76/0.99  thf('25', plain,
% 0.76/0.99      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.76/0.99         ((k2_zfmisc_1 @ (k3_xboole_0 @ X23 @ X25) @ (k3_xboole_0 @ X24 @ X26))
% 0.76/0.99           = (k3_xboole_0 @ (k2_zfmisc_1 @ X23 @ X24) @ 
% 0.76/0.99              (k2_zfmisc_1 @ X25 @ X26)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.76/0.99  thf(idempotence_k3_xboole_0, axiom,
% 0.76/0.99    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.76/0.99  thf('26', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.76/0.99      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.76/0.99  thf('27', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.99  thf('28', plain,
% 0.76/0.99      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.99      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.76/0.99  thf('29', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.99         (((k1_xboole_0) != (k1_xboole_0))
% 0.76/0.99          | ((X1) = (X0))
% 0.76/0.99          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ (k1_tarski @ X1)) @ 
% 0.76/0.99             (k2_zfmisc_1 @ X2 @ (k1_tarski @ X0))))),
% 0.76/0.99      inference('demod', [status(thm)], ['9', '28'])).
% 0.76/0.99  thf('30', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.99         ((r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ (k1_tarski @ X1)) @ 
% 0.76/0.99           (k2_zfmisc_1 @ X2 @ (k1_tarski @ X0)))
% 0.76/0.99          | ((X1) = (X0)))),
% 0.76/0.99      inference('simplify', [status(thm)], ['29'])).
% 0.76/0.99  thf(t131_zfmisc_1, conjecture,
% 0.76/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.99     ( ( ( A ) != ( B ) ) =>
% 0.76/0.99       ( ( r1_xboole_0 @
% 0.76/0.99           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.76/0.99           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 0.76/0.99         ( r1_xboole_0 @
% 0.76/0.99           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.76/0.99           ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.99    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.99        ( ( ( A ) != ( B ) ) =>
% 0.76/0.99          ( ( r1_xboole_0 @
% 0.76/0.99              ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.76/0.99              ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 0.76/0.99            ( r1_xboole_0 @
% 0.76/0.99              ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.76/0.99              ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) )),
% 0.76/0.99    inference('cnf.neg', [status(esa)], [t131_zfmisc_1])).
% 0.76/0.99  thf('31', plain,
% 0.76/0.99      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.76/0.99           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))
% 0.76/0.99        | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.76/0.99             (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('32', plain,
% 0.76/0.99      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.76/0.99           (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))
% 0.76/0.99         <= (~
% 0.76/0.99             ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.76/0.99               (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))))),
% 0.76/0.99      inference('split', [status(esa)], ['31'])).
% 0.76/0.99  thf('33', plain,
% 0.76/0.99      ((((sk_A) = (sk_B)))
% 0.76/0.99         <= (~
% 0.76/0.99             ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.76/0.99               (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['30', '32'])).
% 0.76/0.99  thf('34', plain, (((sk_A) != (sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('35', plain,
% 0.76/0.99      (($false)
% 0.76/0.99         <= (~
% 0.76/0.99             ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.76/0.99               (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))))),
% 0.76/0.99      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.76/0.99  thf('36', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         (((X1) = (X0))
% 0.76/0.99          | ((k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.76/0.99              = (k1_xboole_0)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.99  thf('37', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.99         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.99            != (k1_xboole_0))
% 0.76/0.99          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/0.99  thf('38', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.99         (((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.99            != (k1_xboole_0))
% 0.76/0.99          | ((X3) = (X2))
% 0.76/0.99          | (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X3) @ X1) @ 
% 0.76/0.99             (k2_zfmisc_1 @ (k1_tarski @ X2) @ X0)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['36', '37'])).
% 0.76/0.99  thf('39', plain,
% 0.76/0.99      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.76/0.99         ((k2_zfmisc_1 @ (k4_xboole_0 @ X27 @ X29) @ X28)
% 0.76/0.99           = (k4_xboole_0 @ (k2_zfmisc_1 @ X27 @ X28) @ 
% 0.76/0.99              (k2_zfmisc_1 @ X29 @ X28)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.76/0.99  thf('40', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.99  thf('41', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.99         ((k3_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 0.76/0.99           (k2_zfmisc_1 @ X1 @ X0)) = (k1_xboole_0))),
% 0.76/0.99      inference('sup+', [status(thm)], ['39', '40'])).
% 0.76/0.99  thf('42', plain,
% 0.76/0.99      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.76/0.99         ((k2_zfmisc_1 @ (k3_xboole_0 @ X23 @ X25) @ (k3_xboole_0 @ X24 @ X26))
% 0.76/0.99           = (k3_xboole_0 @ (k2_zfmisc_1 @ X23 @ X24) @ 
% 0.76/0.99              (k2_zfmisc_1 @ X25 @ X26)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.76/0.99  thf('43', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.99  thf('44', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.76/0.99      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.76/0.99  thf('45', plain,
% 0.76/0.99      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.76/0.99      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.76/0.99  thf('46', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.99         (((k1_xboole_0) != (k1_xboole_0))
% 0.76/0.99          | ((X3) = (X2))
% 0.76/0.99          | (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X3) @ X1) @ 
% 0.76/0.99             (k2_zfmisc_1 @ (k1_tarski @ X2) @ X0)))),
% 0.76/0.99      inference('demod', [status(thm)], ['38', '45'])).
% 0.76/0.99  thf('47', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.99         ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X3) @ X1) @ 
% 0.76/0.99           (k2_zfmisc_1 @ (k1_tarski @ X2) @ X0))
% 0.76/0.99          | ((X3) = (X2)))),
% 0.76/0.99      inference('simplify', [status(thm)], ['46'])).
% 0.76/0.99  thf('48', plain,
% 0.76/0.99      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.76/0.99           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))
% 0.76/0.99         <= (~
% 0.76/0.99             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.76/0.99               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))))),
% 0.76/0.99      inference('split', [status(esa)], ['31'])).
% 0.76/0.99  thf('49', plain,
% 0.76/0.99      ((((sk_A) = (sk_B)))
% 0.76/0.99         <= (~
% 0.76/0.99             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.76/0.99               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['47', '48'])).
% 0.76/0.99  thf('50', plain, (((sk_A) != (sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('51', plain,
% 0.76/0.99      (((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.76/0.99         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.76/0.99      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.76/0.99  thf('52', plain,
% 0.76/0.99      (~
% 0.76/0.99       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.76/0.99         (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))) | 
% 0.76/0.99       ~
% 0.76/0.99       ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.76/0.99         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.76/0.99      inference('split', [status(esa)], ['31'])).
% 0.76/0.99  thf('53', plain,
% 0.76/0.99      (~
% 0.76/0.99       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.76/0.99         (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))),
% 0.76/0.99      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.76/0.99  thf('54', plain, ($false),
% 0.76/0.99      inference('simpl_trail', [status(thm)], ['35', '53'])).
% 0.76/0.99  
% 0.76/0.99  % SZS output end Refutation
% 0.76/0.99  
% 0.76/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
