%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.16KYpEjpc9

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:41 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 202 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          : 1117 (2850 expanded)
%              Number of equality atoms :  196 ( 567 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t75_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) )
        = k1_xboole_0 )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) )
          = k1_xboole_0 )
      <=> ~ ( ( A != k1_xboole_0 )
            & ( A
             != ( k1_tarski @ B ) )
            & ( A
             != ( k1_tarski @ C ) )
            & ( A
             != ( k2_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_zfmisc_1])).

thf('0',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('11',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X24 ) @ ( k2_tarski @ X24 @ X25 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t22_zfmisc_1])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X6 )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X14 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('23',plain,(
    ! [X11: $i,X14: $i] :
      ( r2_hidden @ X14 @ ( k2_tarski @ X14 @ X11 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ X18 )
        = X18 )
      | ~ ( r2_hidden @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('26',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_A )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ sk_A @ sk_A )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_C ) )
   <= ( sk_A
      = ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X11 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('37',plain,(
    ! [X11: $i,X14: $i] :
      ( r2_hidden @ X11 @ ( k2_tarski @ X14 @ X11 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ X18 )
        = X18 )
      | ~ ( r2_hidden @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('40',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X24 ) @ ( k2_tarski @ X24 @ X25 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t22_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('45',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ X0 @ sk_C ) )
        = k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup+',[status(thm)],['35','49'])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k1_tarski @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('62',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

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

thf('64',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X22
        = ( k2_tarski @ X20 @ X21 ) )
      | ( X22
        = ( k1_tarski @ X21 ) )
      | ( X22
        = ( k1_tarski @ X20 ) )
      | ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ ( k2_tarski @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('65',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','67'])).

thf('69',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['66','68'])).

thf('70',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['65','69'])).

thf('71',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['58'])).

thf('72',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['56'])).

thf('75',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['54'])).

thf('78',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('81',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X24 ) @ ( k2_tarski @ X24 @ X25 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t22_zfmisc_1])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ X0 ) )
        = k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('87',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','12','34','53','55','57','59','79','85','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.16KYpEjpc9
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:40:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.36/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.53  % Solved by: fo/fo7.sh
% 0.36/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.53  % done 370 iterations in 0.096s
% 0.36/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.53  % SZS output start Refutation
% 0.36/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.53  thf(t75_zfmisc_1, conjecture,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.53       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.36/0.53            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.36/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.53        ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.53          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.36/0.53               ( ( A ) != ( k1_tarski @ C ) ) & 
% 0.36/0.53               ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ) )),
% 0.36/0.53    inference('cnf.neg', [status(esa)], [t75_zfmisc_1])).
% 0.36/0.53  thf('0', plain,
% 0.36/0.53      ((((sk_A) != (k1_xboole_0))
% 0.36/0.53        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('1', plain,
% 0.36/0.53      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.36/0.53       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.36/0.53      inference('split', [status(esa)], ['0'])).
% 0.36/0.53  thf('2', plain,
% 0.36/0.53      ((((sk_A) = (k2_tarski @ sk_B @ sk_C))
% 0.36/0.53        | ((sk_A) = (k1_tarski @ sk_C))
% 0.36/0.53        | ((sk_A) = (k1_tarski @ sk_B))
% 0.36/0.53        | ((sk_A) = (k1_xboole_0))
% 0.36/0.53        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('3', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.53      inference('split', [status(esa)], ['2'])).
% 0.36/0.53  thf(t4_boole, axiom,
% 0.36/0.53    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.53  thf('4', plain,
% 0.36/0.53      (![X10 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.36/0.53      inference('cnf', [status(esa)], [t4_boole])).
% 0.36/0.53  thf('5', plain,
% 0.36/0.53      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))
% 0.36/0.53         <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.36/0.53  thf('6', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.53      inference('split', [status(esa)], ['2'])).
% 0.36/0.53  thf('7', plain,
% 0.36/0.53      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (sk_A)))
% 0.36/0.53         <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.53  thf('8', plain,
% 0.36/0.53      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.36/0.53         <= (~
% 0.36/0.53             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.36/0.53      inference('split', [status(esa)], ['0'])).
% 0.36/0.53  thf('9', plain,
% 0.36/0.53      ((((sk_A) != (k1_xboole_0)))
% 0.36/0.53         <= (~
% 0.36/0.53             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.36/0.53             (((sk_A) = (k1_xboole_0))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.53  thf('10', plain,
% 0.36/0.53      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.36/0.53      inference('split', [status(esa)], ['2'])).
% 0.36/0.53  thf('11', plain,
% 0.36/0.53      ((((sk_A) != (sk_A)))
% 0.36/0.53         <= (~
% 0.36/0.53             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.36/0.53             (((sk_A) = (k1_xboole_0))))),
% 0.36/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.53  thf('12', plain,
% 0.36/0.53      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.36/0.53       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.36/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.53  thf('13', plain,
% 0.36/0.53      ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))
% 0.36/0.53         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.36/0.53      inference('split', [status(esa)], ['2'])).
% 0.36/0.53  thf(t22_zfmisc_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.36/0.53       ( k1_xboole_0 ) ))).
% 0.36/0.53  thf('14', plain,
% 0.36/0.53      (![X24 : $i, X25 : $i]:
% 0.36/0.53         ((k4_xboole_0 @ (k1_tarski @ X24) @ (k2_tarski @ X24 @ X25))
% 0.36/0.53           = (k1_xboole_0))),
% 0.36/0.53      inference('cnf', [status(esa)], [t22_zfmisc_1])).
% 0.36/0.53  thf('15', plain,
% 0.36/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.36/0.53         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.36/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.53  thf(t40_xboole_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.36/0.53  thf('16', plain,
% 0.36/0.53      (![X5 : $i, X6 : $i]:
% 0.36/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X6)
% 0.36/0.53           = (k4_xboole_0 @ X5 @ X6))),
% 0.36/0.53      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.36/0.53  thf(t37_xboole_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.53  thf('17', plain,
% 0.36/0.53      (![X2 : $i, X3 : $i]:
% 0.36/0.53         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.36/0.53      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.36/0.53  thf('18', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.36/0.53          | (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.53  thf('19', plain,
% 0.36/0.53      (((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.53         | (r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ sk_A)))
% 0.36/0.53         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['15', '18'])).
% 0.36/0.53  thf('20', plain,
% 0.36/0.53      (((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ sk_A))
% 0.36/0.53         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.36/0.53      inference('simplify', [status(thm)], ['19'])).
% 0.36/0.53  thf('21', plain,
% 0.36/0.53      ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))
% 0.36/0.53         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.36/0.53      inference('split', [status(esa)], ['2'])).
% 0.36/0.53  thf(d2_tarski, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.36/0.53       ( ![D:$i]:
% 0.36/0.53         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.36/0.53  thf('22', plain,
% 0.36/0.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.53         (((X12) != (X14))
% 0.36/0.53          | (r2_hidden @ X12 @ X13)
% 0.36/0.53          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.36/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.36/0.53  thf('23', plain,
% 0.36/0.53      (![X11 : $i, X14 : $i]: (r2_hidden @ X14 @ (k2_tarski @ X14 @ X11))),
% 0.36/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.36/0.53  thf('24', plain,
% 0.36/0.53      (((r2_hidden @ sk_B @ sk_A)) <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.36/0.53      inference('sup+', [status(thm)], ['21', '23'])).
% 0.36/0.53  thf(l22_zfmisc_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( r2_hidden @ A @ B ) =>
% 0.36/0.53       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.36/0.53  thf('25', plain,
% 0.36/0.53      (![X18 : $i, X19 : $i]:
% 0.36/0.53         (((k2_xboole_0 @ (k1_tarski @ X19) @ X18) = (X18))
% 0.36/0.53          | ~ (r2_hidden @ X19 @ X18))),
% 0.36/0.53      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.36/0.53  thf('26', plain,
% 0.36/0.53      ((((k2_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (sk_A)))
% 0.36/0.53         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.53  thf('27', plain,
% 0.36/0.53      (((r1_tarski @ sk_A @ sk_A)) <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.36/0.53      inference('demod', [status(thm)], ['20', '26'])).
% 0.36/0.53  thf('28', plain,
% 0.36/0.53      (![X2 : $i, X4 : $i]:
% 0.36/0.53         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.36/0.53      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.36/0.53  thf('29', plain,
% 0.36/0.53      ((((k4_xboole_0 @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.36/0.53         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.53  thf('30', plain,
% 0.36/0.53      ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))
% 0.36/0.53         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.36/0.53      inference('split', [status(esa)], ['2'])).
% 0.36/0.53  thf('31', plain,
% 0.36/0.53      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.36/0.53         <= (~
% 0.36/0.53             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.36/0.53      inference('split', [status(esa)], ['0'])).
% 0.36/0.53  thf('32', plain,
% 0.36/0.53      ((((k4_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0)))
% 0.36/0.53         <= (~
% 0.36/0.53             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.36/0.53             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.53  thf('33', plain,
% 0.36/0.53      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.36/0.53         <= (~
% 0.36/0.53             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.36/0.53             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['29', '32'])).
% 0.36/0.53  thf('34', plain,
% 0.36/0.53      (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | 
% 0.36/0.53       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.36/0.53      inference('simplify', [status(thm)], ['33'])).
% 0.36/0.53  thf('35', plain,
% 0.36/0.53      ((((sk_A) = (k1_tarski @ sk_C))) <= ((((sk_A) = (k1_tarski @ sk_C))))),
% 0.36/0.53      inference('split', [status(esa)], ['2'])).
% 0.36/0.53  thf('36', plain,
% 0.36/0.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.53         (((X12) != (X11))
% 0.36/0.53          | (r2_hidden @ X12 @ X13)
% 0.36/0.53          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.36/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.36/0.53  thf('37', plain,
% 0.36/0.53      (![X11 : $i, X14 : $i]: (r2_hidden @ X11 @ (k2_tarski @ X14 @ X11))),
% 0.36/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.36/0.53  thf('38', plain,
% 0.36/0.53      (![X18 : $i, X19 : $i]:
% 0.36/0.53         (((k2_xboole_0 @ (k1_tarski @ X19) @ X18) = (X18))
% 0.36/0.53          | ~ (r2_hidden @ X19 @ X18))),
% 0.36/0.53      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.36/0.53  thf('39', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.36/0.53           = (k2_tarski @ X1 @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.53  thf(t69_enumset1, axiom,
% 0.36/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.53  thf('40', plain,
% 0.36/0.53      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.36/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.53  thf('41', plain,
% 0.36/0.53      (![X24 : $i, X25 : $i]:
% 0.36/0.53         ((k4_xboole_0 @ (k1_tarski @ X24) @ (k2_tarski @ X24 @ X25))
% 0.36/0.53           = (k1_xboole_0))),
% 0.36/0.53      inference('cnf', [status(esa)], [t22_zfmisc_1])).
% 0.36/0.53  thf('42', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.36/0.53      inference('sup+', [status(thm)], ['40', '41'])).
% 0.36/0.53  thf(t44_xboole_1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.36/0.53       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.53  thf('43', plain,
% 0.36/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.53         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.36/0.53          | ~ (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.36/0.53      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.36/0.53  thf('44', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.36/0.53          | (r1_tarski @ (k1_tarski @ X1) @ 
% 0.36/0.53             (k2_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.53  thf('45', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.36/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.53  thf('46', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         (r1_tarski @ (k1_tarski @ X1) @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.36/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.53  thf('47', plain,
% 0.36/0.53      (![X2 : $i, X4 : $i]:
% 0.36/0.53         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.36/0.53      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.36/0.53  thf('48', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         ((k4_xboole_0 @ (k1_tarski @ X1) @ 
% 0.36/0.53           (k2_xboole_0 @ (k1_tarski @ X1) @ X0)) = (k1_xboole_0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.53  thf('49', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.36/0.53           = (k1_xboole_0))),
% 0.36/0.53      inference('sup+', [status(thm)], ['39', '48'])).
% 0.36/0.53  thf('50', plain,
% 0.36/0.53      ((![X0 : $i]:
% 0.36/0.53          ((k4_xboole_0 @ sk_A @ (k2_tarski @ X0 @ sk_C)) = (k1_xboole_0)))
% 0.36/0.53         <= ((((sk_A) = (k1_tarski @ sk_C))))),
% 0.36/0.53      inference('sup+', [status(thm)], ['35', '49'])).
% 0.36/0.53  thf('51', plain,
% 0.36/0.53      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.36/0.53         <= (~
% 0.36/0.53             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.36/0.53      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf('52', plain,
% 0.36/0.54      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.36/0.54             (((sk_A) = (k1_tarski @ sk_C))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      (~ (((sk_A) = (k1_tarski @ sk_C))) | 
% 0.36/0.54       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['52'])).
% 0.36/0.54  thf('54', plain,
% 0.36/0.54      ((((sk_A) != (k1_tarski @ sk_B))
% 0.36/0.54        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('55', plain,
% 0.36/0.54      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.36/0.54       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.36/0.54      inference('split', [status(esa)], ['54'])).
% 0.36/0.54  thf('56', plain,
% 0.36/0.54      ((((sk_A) != (k1_tarski @ sk_C))
% 0.36/0.54        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('57', plain,
% 0.36/0.54      (~ (((sk_A) = (k1_tarski @ sk_C))) | 
% 0.36/0.54       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.36/0.54      inference('split', [status(esa)], ['56'])).
% 0.36/0.54  thf('58', plain,
% 0.36/0.54      ((((sk_A) != (k2_tarski @ sk_B @ sk_C))
% 0.36/0.54        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('59', plain,
% 0.36/0.54      (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | 
% 0.36/0.54       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.36/0.54      inference('split', [status(esa)], ['58'])).
% 0.36/0.54  thf('60', plain,
% 0.36/0.54      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))
% 0.36/0.54         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.36/0.54      inference('split', [status(esa)], ['2'])).
% 0.36/0.54  thf('61', plain,
% 0.36/0.54      (![X2 : $i, X3 : $i]:
% 0.36/0.54         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.36/0.54  thf('62', plain,
% 0.36/0.54      (((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.54         | (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))
% 0.36/0.54         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['60', '61'])).
% 0.36/0.54  thf('63', plain,
% 0.36/0.54      (((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))
% 0.36/0.54         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.36/0.54      inference('simplify', [status(thm)], ['62'])).
% 0.36/0.54  thf(l45_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.36/0.54       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.36/0.54            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.36/0.54  thf('64', plain,
% 0.36/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.54         (((X22) = (k2_tarski @ X20 @ X21))
% 0.36/0.54          | ((X22) = (k1_tarski @ X21))
% 0.36/0.54          | ((X22) = (k1_tarski @ X20))
% 0.36/0.54          | ((X22) = (k1_xboole_0))
% 0.36/0.54          | ~ (r1_tarski @ X22 @ (k2_tarski @ X20 @ X21)))),
% 0.36/0.54      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.36/0.54  thf('65', plain,
% 0.36/0.54      (((((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_A) = (k1_tarski @ sk_B))
% 0.36/0.54         | ((sk_A) = (k1_tarski @ sk_C))
% 0.36/0.54         | ((sk_A) = (k2_tarski @ sk_B @ sk_C))))
% 0.36/0.54         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['63', '64'])).
% 0.36/0.54  thf('66', plain,
% 0.36/0.54      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.36/0.54      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf('67', plain,
% 0.36/0.54      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.36/0.54       ~ (((sk_A) = (k1_xboole_0)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.54  thf('68', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.36/0.54      inference('sat_resolution*', [status(thm)], ['1', '67'])).
% 0.36/0.54  thf('69', plain, (((sk_A) != (k1_xboole_0))),
% 0.36/0.54      inference('simpl_trail', [status(thm)], ['66', '68'])).
% 0.36/0.54  thf('70', plain,
% 0.36/0.54      (((((sk_A) = (k1_tarski @ sk_B))
% 0.36/0.54         | ((sk_A) = (k1_tarski @ sk_C))
% 0.36/0.54         | ((sk_A) = (k2_tarski @ sk_B @ sk_C))))
% 0.36/0.54         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['65', '69'])).
% 0.36/0.54  thf('71', plain,
% 0.36/0.54      ((((sk_A) != (k2_tarski @ sk_B @ sk_C)))
% 0.36/0.54         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.36/0.54      inference('split', [status(esa)], ['58'])).
% 0.36/0.54  thf('72', plain,
% 0.36/0.54      (((((sk_A) != (sk_A))
% 0.36/0.54         | ((sk_A) = (k1_tarski @ sk_C))
% 0.36/0.54         | ((sk_A) = (k1_tarski @ sk_B))))
% 0.36/0.54         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.36/0.54             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['70', '71'])).
% 0.36/0.54  thf('73', plain,
% 0.36/0.54      (((((sk_A) = (k1_tarski @ sk_B)) | ((sk_A) = (k1_tarski @ sk_C))))
% 0.36/0.54         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.36/0.54             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.36/0.54      inference('simplify', [status(thm)], ['72'])).
% 0.36/0.54  thf('74', plain,
% 0.36/0.54      ((((sk_A) != (k1_tarski @ sk_C))) <= (~ (((sk_A) = (k1_tarski @ sk_C))))),
% 0.36/0.54      inference('split', [status(esa)], ['56'])).
% 0.36/0.54  thf('75', plain,
% 0.36/0.54      (((((sk_A) != (sk_A)) | ((sk_A) = (k1_tarski @ sk_B))))
% 0.36/0.54         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.36/0.54             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.36/0.54             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['73', '74'])).
% 0.36/0.54  thf('76', plain,
% 0.36/0.54      ((((sk_A) = (k1_tarski @ sk_B)))
% 0.36/0.54         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.36/0.54             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.36/0.54             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.36/0.54      inference('simplify', [status(thm)], ['75'])).
% 0.36/0.54  thf('77', plain,
% 0.36/0.54      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.36/0.54      inference('split', [status(esa)], ['54'])).
% 0.36/0.54  thf('78', plain,
% 0.36/0.54      ((((sk_A) != (sk_A)))
% 0.36/0.54         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.36/0.54             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.36/0.54             ~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.36/0.54             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['76', '77'])).
% 0.36/0.54  thf('79', plain,
% 0.36/0.54      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.36/0.54       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.36/0.54       (((sk_A) = (k1_tarski @ sk_C))) | (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['78'])).
% 0.36/0.54  thf('80', plain,
% 0.36/0.54      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.36/0.54      inference('split', [status(esa)], ['2'])).
% 0.36/0.54  thf('81', plain,
% 0.36/0.54      (![X24 : $i, X25 : $i]:
% 0.36/0.54         ((k4_xboole_0 @ (k1_tarski @ X24) @ (k2_tarski @ X24 @ X25))
% 0.36/0.54           = (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t22_zfmisc_1])).
% 0.36/0.54  thf('82', plain,
% 0.36/0.54      ((![X0 : $i]:
% 0.36/0.54          ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ X0)) = (k1_xboole_0)))
% 0.36/0.54         <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.36/0.54      inference('sup+', [status(thm)], ['80', '81'])).
% 0.36/0.54  thf('83', plain,
% 0.36/0.54      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.36/0.54      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf('84', plain,
% 0.36/0.54      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.36/0.54             (((sk_A) = (k1_tarski @ sk_B))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['82', '83'])).
% 0.36/0.54  thf('85', plain,
% 0.36/0.54      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.36/0.54       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['84'])).
% 0.36/0.54  thf('86', plain,
% 0.36/0.54      ((((sk_A) = (k1_tarski @ sk_B))) | (((sk_A) = (k1_tarski @ sk_C))) | 
% 0.36/0.54       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.36/0.54       (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | (((sk_A) = (k1_xboole_0)))),
% 0.36/0.54      inference('split', [status(esa)], ['2'])).
% 0.36/0.54  thf('87', plain, ($false),
% 0.36/0.54      inference('sat_resolution*', [status(thm)],
% 0.36/0.54                ['1', '12', '34', '53', '55', '57', '59', '79', '85', '86'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
