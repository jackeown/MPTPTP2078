%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gpjAqGnuW6

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:38 EST 2020

% Result     : Theorem 38.71s
% Output     : Refutation 38.71s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 398 expanded)
%              Number of leaves         :   12 ( 102 expanded)
%              Depth                    :   18
%              Number of atoms          : 1273 (4371 expanded)
%              Number of equality atoms :   90 ( 337 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ( X13 = X12 )
      | ( X13 = X9 )
      | ( X11
       != ( k2_tarski @ X12 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('13',plain,(
    ! [X9: $i,X12: $i,X13: $i] :
      ( ( X13 = X9 )
      | ( X13 = X12 )
      | ~ ( r2_hidden @ X13 @ ( k2_tarski @ X12 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 )
        = k1_xboole_0 )
      | ( ( sk_D @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) @ X2 @ k1_xboole_0 )
        = X1 )
      | ( ( sk_D @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) @ X2 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 ) )
      | ( ( sk_D @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 ) @ X3 @ k1_xboole_0 )
        = X2 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = k1_xboole_0 )
      | ( ( sk_D @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 ) @ X3 @ k1_xboole_0 )
        = X2 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['18'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('26',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t73_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = k1_xboole_0 )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_zfmisc_1])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('33',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ X1 )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ X0 ) @ X1 ) ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('35',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X12 )
      | ( r2_hidden @ X10 @ X11 )
      | ( X11
       != ( k2_tarski @ X12 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('36',plain,(
    ! [X9: $i,X12: $i] :
      ( r2_hidden @ X12 @ ( k2_tarski @ X12 @ X9 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( r2_hidden @ sk_A @ k1_xboole_0 )
      | ( r2_hidden @ sk_A @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X9 )
      | ( r2_hidden @ X10 @ X11 )
      | ( X11
       != ( k2_tarski @ X12 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('47',plain,(
    ! [X9: $i,X12: $i] :
      ( r2_hidden @ X9 @ ( k2_tarski @ X12 @ X9 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( r2_hidden @ sk_B @ k1_xboole_0 )
      | ( r2_hidden @ sk_B @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('52',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['42'])).

thf('54',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['42'])).

thf('56',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('57',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['44','54','55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ X1 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ X0 ) @ X1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['33','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['18'])).

thf('60',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('63',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ X1 )
      | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ sk_C @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ sk_C @ X0 ) ) )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(condensation,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      | ( r2_hidden @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('73',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_C ) @ X1 @ k1_xboole_0 )
        = X0 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','73'])).

thf('75',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('76',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('86',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['78','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_C ) )
      | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_C )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['74','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_C )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('91',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ X0 )
        | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_C @ X0 ) ) )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('96',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ sk_B @ X0 )
        | ( r2_hidden @ sk_B @ X1 )
        | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ X0 ) @ X1 ) ) )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['91'])).

thf('98',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['44','54','55','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ X1 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ X0 ) @ X1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['96','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ X1 )
      | ~ ( r2_hidden @ sk_B @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ sk_C @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_B @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ sk_C @ X0 ) ) )
      | ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(condensation,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) )
      | ( r2_hidden @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('105',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['89','105'])).

thf('107',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('108',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['44','54','55'])).

thf('109',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['106','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gpjAqGnuW6
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 38.71/38.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 38.71/38.97  % Solved by: fo/fo7.sh
% 38.71/38.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 38.71/38.97  % done 28871 iterations in 38.515s
% 38.71/38.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 38.71/38.97  % SZS output start Refutation
% 38.71/38.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 38.71/38.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 38.71/38.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 38.71/38.97  thf(sk_C_type, type, sk_C: $i).
% 38.71/38.97  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 38.71/38.97  thf(sk_B_type, type, sk_B: $i).
% 38.71/38.97  thf(sk_A_type, type, sk_A: $i).
% 38.71/38.97  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 38.71/38.97  thf(d5_xboole_0, axiom,
% 38.71/38.97    (![A:$i,B:$i,C:$i]:
% 38.71/38.97     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 38.71/38.97       ( ![D:$i]:
% 38.71/38.97         ( ( r2_hidden @ D @ C ) <=>
% 38.71/38.97           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 38.71/38.97  thf('0', plain,
% 38.71/38.97      (![X1 : $i, X2 : $i, X5 : $i]:
% 38.71/38.97         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 38.71/38.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 38.71/38.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 38.71/38.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 38.71/38.97  thf(t4_boole, axiom,
% 38.71/38.97    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 38.71/38.97  thf('1', plain,
% 38.71/38.97      (![X8 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 38.71/38.97      inference('cnf', [status(esa)], [t4_boole])).
% 38.71/38.97  thf('2', plain,
% 38.71/38.97      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 38.71/38.97         (~ (r2_hidden @ X4 @ X3)
% 38.71/38.97          | ~ (r2_hidden @ X4 @ X2)
% 38.71/38.97          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 38.71/38.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 38.71/38.97  thf('3', plain,
% 38.71/38.97      (![X1 : $i, X2 : $i, X4 : $i]:
% 38.71/38.97         (~ (r2_hidden @ X4 @ X2)
% 38.71/38.97          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 38.71/38.97      inference('simplify', [status(thm)], ['2'])).
% 38.71/38.97  thf('4', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 38.71/38.97      inference('sup-', [status(thm)], ['1', '3'])).
% 38.71/38.97  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 38.71/38.97      inference('condensation', [status(thm)], ['4'])).
% 38.71/38.97  thf('6', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 38.71/38.97          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['0', '5'])).
% 38.71/38.97  thf('7', plain,
% 38.71/38.97      (![X8 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 38.71/38.97      inference('cnf', [status(esa)], [t4_boole])).
% 38.71/38.97  thf('8', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 38.71/38.97          | ((X1) = (k1_xboole_0)))),
% 38.71/38.97      inference('demod', [status(thm)], ['6', '7'])).
% 38.71/38.97  thf('9', plain,
% 38.71/38.97      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 38.71/38.97         (~ (r2_hidden @ X4 @ X3)
% 38.71/38.97          | (r2_hidden @ X4 @ X1)
% 38.71/38.97          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 38.71/38.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 38.71/38.97  thf('10', plain,
% 38.71/38.97      (![X1 : $i, X2 : $i, X4 : $i]:
% 38.71/38.97         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 38.71/38.97      inference('simplify', [status(thm)], ['9'])).
% 38.71/38.97  thf('11', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.71/38.97         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 38.71/38.97          | (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 38.71/38.97             X1))),
% 38.71/38.97      inference('sup-', [status(thm)], ['8', '10'])).
% 38.71/38.97  thf(d2_tarski, axiom,
% 38.71/38.97    (![A:$i,B:$i,C:$i]:
% 38.71/38.97     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 38.71/38.97       ( ![D:$i]:
% 38.71/38.97         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 38.71/38.97  thf('12', plain,
% 38.71/38.97      (![X9 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 38.71/38.97         (~ (r2_hidden @ X13 @ X11)
% 38.71/38.97          | ((X13) = (X12))
% 38.71/38.97          | ((X13) = (X9))
% 38.71/38.97          | ((X11) != (k2_tarski @ X12 @ X9)))),
% 38.71/38.97      inference('cnf', [status(esa)], [d2_tarski])).
% 38.71/38.97  thf('13', plain,
% 38.71/38.97      (![X9 : $i, X12 : $i, X13 : $i]:
% 38.71/38.97         (((X13) = (X9))
% 38.71/38.97          | ((X13) = (X12))
% 38.71/38.97          | ~ (r2_hidden @ X13 @ (k2_tarski @ X12 @ X9)))),
% 38.71/38.97      inference('simplify', [status(thm)], ['12'])).
% 38.71/38.97  thf('14', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 38.71/38.97         (((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3) = (k1_xboole_0))
% 38.71/38.97          | ((sk_D @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3) @ X2 @ 
% 38.71/38.97              k1_xboole_0) = (X1))
% 38.71/38.97          | ((sk_D @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3) @ X2 @ 
% 38.71/38.97              k1_xboole_0) = (X0)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['11', '13'])).
% 38.71/38.97  thf('15', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 38.71/38.97          | ((X1) = (k1_xboole_0)))),
% 38.71/38.97      inference('demod', [status(thm)], ['6', '7'])).
% 38.71/38.97  thf('16', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 38.71/38.97         ((r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1))
% 38.71/38.97          | ((sk_D @ (k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1) @ X3 @ 
% 38.71/38.97              k1_xboole_0) = (X2))
% 38.71/38.97          | ((k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1) = (k1_xboole_0))
% 38.71/38.97          | ((k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1) = (k1_xboole_0)))),
% 38.71/38.97      inference('sup+', [status(thm)], ['14', '15'])).
% 38.71/38.97  thf('17', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 38.71/38.97         (((k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1) = (k1_xboole_0))
% 38.71/38.97          | ((sk_D @ (k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1) @ X3 @ 
% 38.71/38.97              k1_xboole_0) = (X2))
% 38.71/38.97          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1)))),
% 38.71/38.97      inference('simplify', [status(thm)], ['16'])).
% 38.71/38.97  thf('18', plain,
% 38.71/38.97      (![X1 : $i, X2 : $i, X5 : $i]:
% 38.71/38.97         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 38.71/38.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 38.71/38.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 38.71/38.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 38.71/38.97  thf('19', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 38.71/38.97          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 38.71/38.97      inference('eq_fact', [status(thm)], ['18'])).
% 38.71/38.97  thf('20', plain,
% 38.71/38.97      (![X1 : $i, X2 : $i, X5 : $i]:
% 38.71/38.97         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 38.71/38.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 38.71/38.97          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 38.71/38.97          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 38.71/38.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 38.71/38.97  thf('21', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 38.71/38.97          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 38.71/38.97          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 38.71/38.97          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['19', '20'])).
% 38.71/38.97  thf('22', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 38.71/38.97          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 38.71/38.97          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 38.71/38.97      inference('simplify', [status(thm)], ['21'])).
% 38.71/38.97  thf('23', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 38.71/38.97          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 38.71/38.97      inference('eq_fact', [status(thm)], ['18'])).
% 38.71/38.97  thf('24', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 38.71/38.97          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 38.71/38.97      inference('clc', [status(thm)], ['22', '23'])).
% 38.71/38.97  thf('25', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 38.71/38.97      inference('condensation', [status(thm)], ['4'])).
% 38.71/38.97  thf('26', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 38.71/38.97      inference('sup-', [status(thm)], ['24', '25'])).
% 38.71/38.97  thf(t73_zfmisc_1, conjecture,
% 38.71/38.97    (![A:$i,B:$i,C:$i]:
% 38.71/38.97     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 38.71/38.97       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 38.71/38.97  thf(zf_stmt_0, negated_conjecture,
% 38.71/38.97    (~( ![A:$i,B:$i,C:$i]:
% 38.71/38.97        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 38.71/38.97          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 38.71/38.97    inference('cnf.neg', [status(esa)], [t73_zfmisc_1])).
% 38.71/38.97  thf('27', plain,
% 38.71/38.97      (((r2_hidden @ sk_A @ sk_C)
% 38.71/38.97        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 38.71/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.71/38.97  thf('28', plain,
% 38.71/38.97      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 38.71/38.97      inference('split', [status(esa)], ['27'])).
% 38.71/38.97  thf('29', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 38.71/38.97         (~ (r2_hidden @ X0 @ X1)
% 38.71/38.97          | (r2_hidden @ X0 @ X2)
% 38.71/38.97          | (r2_hidden @ X0 @ X3)
% 38.71/38.97          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 38.71/38.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 38.71/38.97  thf('30', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.71/38.97         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 38.71/38.97          | (r2_hidden @ X0 @ X2)
% 38.71/38.97          | ~ (r2_hidden @ X0 @ X1))),
% 38.71/38.97      inference('simplify', [status(thm)], ['29'])).
% 38.71/38.97  thf('31', plain,
% 38.71/38.97      ((![X0 : $i]:
% 38.71/38.97          ((r2_hidden @ sk_A @ X0)
% 38.71/38.97           | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_C @ X0))))
% 38.71/38.97         <= (((r2_hidden @ sk_A @ sk_C)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['28', '30'])).
% 38.71/38.97  thf('32', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.71/38.97         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 38.71/38.97          | (r2_hidden @ X0 @ X2)
% 38.71/38.97          | ~ (r2_hidden @ X0 @ X1))),
% 38.71/38.97      inference('simplify', [status(thm)], ['29'])).
% 38.71/38.97  thf('33', plain,
% 38.71/38.97      ((![X0 : $i, X1 : $i]:
% 38.71/38.97          ((r2_hidden @ sk_A @ X0)
% 38.71/38.97           | (r2_hidden @ sk_A @ X1)
% 38.71/38.97           | (r2_hidden @ sk_A @ (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ X0) @ X1))))
% 38.71/38.97         <= (((r2_hidden @ sk_A @ sk_C)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['31', '32'])).
% 38.71/38.97  thf('34', plain,
% 38.71/38.97      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))
% 38.71/38.97         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 38.71/38.97      inference('split', [status(esa)], ['27'])).
% 38.71/38.97  thf('35', plain,
% 38.71/38.97      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 38.71/38.97         (((X10) != (X12))
% 38.71/38.97          | (r2_hidden @ X10 @ X11)
% 38.71/38.97          | ((X11) != (k2_tarski @ X12 @ X9)))),
% 38.71/38.97      inference('cnf', [status(esa)], [d2_tarski])).
% 38.71/38.97  thf('36', plain,
% 38.71/38.97      (![X9 : $i, X12 : $i]: (r2_hidden @ X12 @ (k2_tarski @ X12 @ X9))),
% 38.71/38.97      inference('simplify', [status(thm)], ['35'])).
% 38.71/38.97  thf('37', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.71/38.97         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 38.71/38.97          | (r2_hidden @ X0 @ X2)
% 38.71/38.97          | ~ (r2_hidden @ X0 @ X1))),
% 38.71/38.97      inference('simplify', [status(thm)], ['29'])).
% 38.71/38.97  thf('38', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.71/38.97         ((r2_hidden @ X1 @ X2)
% 38.71/38.97          | (r2_hidden @ X1 @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['36', '37'])).
% 38.71/38.97  thf('39', plain,
% 38.71/38.97      ((((r2_hidden @ sk_A @ k1_xboole_0) | (r2_hidden @ sk_A @ sk_C)))
% 38.71/38.97         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 38.71/38.97      inference('sup+', [status(thm)], ['34', '38'])).
% 38.71/38.97  thf('40', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 38.71/38.97      inference('condensation', [status(thm)], ['4'])).
% 38.71/38.97  thf('41', plain,
% 38.71/38.97      (((r2_hidden @ sk_A @ sk_C))
% 38.71/38.97         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 38.71/38.97      inference('clc', [status(thm)], ['39', '40'])).
% 38.71/38.97  thf('42', plain,
% 38.71/38.97      ((~ (r2_hidden @ sk_B @ sk_C)
% 38.71/38.97        | ~ (r2_hidden @ sk_A @ sk_C)
% 38.71/38.97        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_xboole_0)))),
% 38.71/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.71/38.97  thf('43', plain,
% 38.71/38.97      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 38.71/38.97      inference('split', [status(esa)], ['42'])).
% 38.71/38.97  thf('44', plain,
% 38.71/38.97      (((r2_hidden @ sk_A @ sk_C)) | 
% 38.71/38.97       ~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['41', '43'])).
% 38.71/38.97  thf('45', plain,
% 38.71/38.97      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))
% 38.71/38.97         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 38.71/38.97      inference('split', [status(esa)], ['27'])).
% 38.71/38.97  thf('46', plain,
% 38.71/38.97      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 38.71/38.97         (((X10) != (X9))
% 38.71/38.97          | (r2_hidden @ X10 @ X11)
% 38.71/38.97          | ((X11) != (k2_tarski @ X12 @ X9)))),
% 38.71/38.97      inference('cnf', [status(esa)], [d2_tarski])).
% 38.71/38.97  thf('47', plain,
% 38.71/38.97      (![X9 : $i, X12 : $i]: (r2_hidden @ X9 @ (k2_tarski @ X12 @ X9))),
% 38.71/38.97      inference('simplify', [status(thm)], ['46'])).
% 38.71/38.97  thf('48', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.71/38.97         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 38.71/38.97          | (r2_hidden @ X0 @ X2)
% 38.71/38.97          | ~ (r2_hidden @ X0 @ X1))),
% 38.71/38.97      inference('simplify', [status(thm)], ['29'])).
% 38.71/38.97  thf('49', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.71/38.97         ((r2_hidden @ X0 @ X2)
% 38.71/38.97          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['47', '48'])).
% 38.71/38.97  thf('50', plain,
% 38.71/38.97      ((((r2_hidden @ sk_B @ k1_xboole_0) | (r2_hidden @ sk_B @ sk_C)))
% 38.71/38.97         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 38.71/38.97      inference('sup+', [status(thm)], ['45', '49'])).
% 38.71/38.97  thf('51', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 38.71/38.97      inference('condensation', [status(thm)], ['4'])).
% 38.71/38.97  thf('52', plain,
% 38.71/38.97      (((r2_hidden @ sk_B @ sk_C))
% 38.71/38.97         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 38.71/38.97      inference('clc', [status(thm)], ['50', '51'])).
% 38.71/38.97  thf('53', plain,
% 38.71/38.97      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 38.71/38.97      inference('split', [status(esa)], ['42'])).
% 38.71/38.97  thf('54', plain,
% 38.71/38.97      (((r2_hidden @ sk_B @ sk_C)) | 
% 38.71/38.97       ~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['52', '53'])).
% 38.71/38.97  thf('55', plain,
% 38.71/38.97      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 38.71/38.97       ~ ((r2_hidden @ sk_A @ sk_C)) | ~ ((r2_hidden @ sk_B @ sk_C))),
% 38.71/38.97      inference('split', [status(esa)], ['42'])).
% 38.71/38.97  thf('56', plain,
% 38.71/38.97      (((r2_hidden @ sk_A @ sk_C)) | 
% 38.71/38.97       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 38.71/38.97      inference('split', [status(esa)], ['27'])).
% 38.71/38.97  thf('57', plain, (((r2_hidden @ sk_A @ sk_C))),
% 38.71/38.97      inference('sat_resolution*', [status(thm)], ['44', '54', '55', '56'])).
% 38.71/38.97  thf('58', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         ((r2_hidden @ sk_A @ X0)
% 38.71/38.97          | (r2_hidden @ sk_A @ X1)
% 38.71/38.97          | (r2_hidden @ sk_A @ (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ X0) @ X1)))),
% 38.71/38.97      inference('simpl_trail', [status(thm)], ['33', '57'])).
% 38.71/38.97  thf('59', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 38.71/38.97          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 38.71/38.97      inference('eq_fact', [status(thm)], ['18'])).
% 38.71/38.97  thf('60', plain,
% 38.71/38.97      (![X1 : $i, X2 : $i, X4 : $i]:
% 38.71/38.97         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 38.71/38.97      inference('simplify', [status(thm)], ['9'])).
% 38.71/38.97  thf('61', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.71/38.97         (((k4_xboole_0 @ X1 @ X0)
% 38.71/38.97            = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 38.71/38.97          | (r2_hidden @ 
% 38.71/38.97             (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 38.71/38.97             X1))),
% 38.71/38.97      inference('sup-', [status(thm)], ['59', '60'])).
% 38.71/38.97  thf('62', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 38.71/38.97          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 38.71/38.97      inference('clc', [status(thm)], ['22', '23'])).
% 38.71/38.97  thf('63', plain,
% 38.71/38.97      (![X1 : $i, X2 : $i, X4 : $i]:
% 38.71/38.97         (~ (r2_hidden @ X4 @ X2)
% 38.71/38.97          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 38.71/38.97      inference('simplify', [status(thm)], ['2'])).
% 38.71/38.97  thf('64', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.71/38.97         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 38.71/38.97          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 38.71/38.97      inference('sup-', [status(thm)], ['62', '63'])).
% 38.71/38.97  thf('65', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.71/38.97         (((k4_xboole_0 @ X0 @ X1)
% 38.71/38.97            = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0)))
% 38.71/38.97          | ((k4_xboole_0 @ X0 @ X1)
% 38.71/38.97              = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 38.71/38.97                 (k4_xboole_0 @ X2 @ X0))))),
% 38.71/38.97      inference('sup-', [status(thm)], ['61', '64'])).
% 38.71/38.97  thf('66', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.71/38.97         ((k4_xboole_0 @ X0 @ X1)
% 38.71/38.97           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0)))),
% 38.71/38.97      inference('simplify', [status(thm)], ['65'])).
% 38.71/38.97  thf('67', plain,
% 38.71/38.97      (![X1 : $i, X2 : $i, X4 : $i]:
% 38.71/38.97         (~ (r2_hidden @ X4 @ X2)
% 38.71/38.97          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 38.71/38.97      inference('simplify', [status(thm)], ['2'])).
% 38.71/38.97  thf('68', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 38.71/38.97         (~ (r2_hidden @ X3 @ (k4_xboole_0 @ X1 @ X0))
% 38.71/38.97          | ~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ X1)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['66', '67'])).
% 38.71/38.97  thf('69', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.71/38.97         ((r2_hidden @ sk_A @ X0)
% 38.71/38.97          | (r2_hidden @ sk_A @ X1)
% 38.71/38.97          | ~ (r2_hidden @ sk_A @ 
% 38.71/38.97               (k4_xboole_0 @ X2 @ (k4_xboole_0 @ sk_C @ X1))))),
% 38.71/38.97      inference('sup-', [status(thm)], ['58', '68'])).
% 38.71/38.97  thf('70', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         (~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ sk_C @ X0)))
% 38.71/38.97          | (r2_hidden @ sk_A @ X0))),
% 38.71/38.97      inference('condensation', [status(thm)], ['69'])).
% 38.71/38.97  thf('71', plain,
% 38.71/38.97      (![X0 : $i]:
% 38.71/38.97         (~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 38.71/38.97          | (r2_hidden @ sk_A @ k1_xboole_0))),
% 38.71/38.97      inference('sup-', [status(thm)], ['26', '70'])).
% 38.71/38.97  thf('72', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 38.71/38.97      inference('condensation', [status(thm)], ['4'])).
% 38.71/38.97  thf('73', plain,
% 38.71/38.97      (![X0 : $i]: ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))),
% 38.71/38.97      inference('clc', [status(thm)], ['71', '72'])).
% 38.71/38.97  thf('74', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         (((sk_D @ (k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C) @ X1 @ 
% 38.71/38.97            k1_xboole_0) = (X0))
% 38.71/38.97          | ((k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C) = (k1_xboole_0)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['17', '73'])).
% 38.71/38.97  thf('75', plain,
% 38.71/38.97      (![X1 : $i, X2 : $i, X5 : $i]:
% 38.71/38.97         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 38.71/38.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 38.71/38.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 38.71/38.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 38.71/38.97  thf('76', plain,
% 38.71/38.97      (![X1 : $i, X2 : $i, X5 : $i]:
% 38.71/38.97         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 38.71/38.97          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 38.71/38.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 38.71/38.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 38.71/38.97  thf('77', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 38.71/38.97          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 38.71/38.97          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 38.71/38.97          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['75', '76'])).
% 38.71/38.97  thf('78', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 38.71/38.97          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 38.71/38.97      inference('simplify', [status(thm)], ['77'])).
% 38.71/38.97  thf('79', plain,
% 38.71/38.97      (![X1 : $i, X2 : $i, X5 : $i]:
% 38.71/38.97         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 38.71/38.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 38.71/38.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 38.71/38.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 38.71/38.97  thf('80', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 38.71/38.97      inference('condensation', [status(thm)], ['4'])).
% 38.71/38.97  thf('81', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 38.71/38.97          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['79', '80'])).
% 38.71/38.97  thf('82', plain,
% 38.71/38.97      (![X1 : $i, X2 : $i, X5 : $i]:
% 38.71/38.97         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 38.71/38.97          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 38.71/38.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 38.71/38.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 38.71/38.97  thf('83', plain,
% 38.71/38.97      (![X0 : $i]:
% 38.71/38.97         (((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))
% 38.71/38.97          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 38.71/38.97          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['81', '82'])).
% 38.71/38.97  thf('84', plain,
% 38.71/38.97      (![X0 : $i]:
% 38.71/38.97         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 38.71/38.97          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 38.71/38.97      inference('simplify', [status(thm)], ['83'])).
% 38.71/38.97  thf('85', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 38.71/38.97      inference('condensation', [status(thm)], ['4'])).
% 38.71/38.97  thf('86', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 38.71/38.97      inference('clc', [status(thm)], ['84', '85'])).
% 38.71/38.97  thf('87', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 38.71/38.97      inference('demod', [status(thm)], ['78', '86'])).
% 38.71/38.97  thf('88', plain,
% 38.71/38.97      (![X0 : $i]:
% 38.71/38.97         ((r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C))
% 38.71/38.97          | ((k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C) = (k1_xboole_0))
% 38.71/38.97          | ((k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C) = (k1_xboole_0)))),
% 38.71/38.97      inference('sup+', [status(thm)], ['74', '87'])).
% 38.71/38.97  thf('89', plain,
% 38.71/38.97      (![X0 : $i]:
% 38.71/38.97         (((k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C) = (k1_xboole_0))
% 38.71/38.97          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C)))),
% 38.71/38.97      inference('simplify', [status(thm)], ['88'])).
% 38.71/38.97  thf('90', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 38.71/38.97      inference('sup-', [status(thm)], ['24', '25'])).
% 38.71/38.97  thf('91', plain,
% 38.71/38.97      (((r2_hidden @ sk_B @ sk_C)
% 38.71/38.97        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 38.71/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.71/38.97  thf('92', plain,
% 38.71/38.97      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 38.71/38.97      inference('split', [status(esa)], ['91'])).
% 38.71/38.97  thf('93', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.71/38.97         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 38.71/38.97          | (r2_hidden @ X0 @ X2)
% 38.71/38.97          | ~ (r2_hidden @ X0 @ X1))),
% 38.71/38.97      inference('simplify', [status(thm)], ['29'])).
% 38.71/38.97  thf('94', plain,
% 38.71/38.97      ((![X0 : $i]:
% 38.71/38.97          ((r2_hidden @ sk_B @ X0)
% 38.71/38.97           | (r2_hidden @ sk_B @ (k4_xboole_0 @ sk_C @ X0))))
% 38.71/38.97         <= (((r2_hidden @ sk_B @ sk_C)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['92', '93'])).
% 38.71/38.97  thf('95', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.71/38.97         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 38.71/38.97          | (r2_hidden @ X0 @ X2)
% 38.71/38.97          | ~ (r2_hidden @ X0 @ X1))),
% 38.71/38.97      inference('simplify', [status(thm)], ['29'])).
% 38.71/38.97  thf('96', plain,
% 38.71/38.97      ((![X0 : $i, X1 : $i]:
% 38.71/38.97          ((r2_hidden @ sk_B @ X0)
% 38.71/38.97           | (r2_hidden @ sk_B @ X1)
% 38.71/38.97           | (r2_hidden @ sk_B @ (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ X0) @ X1))))
% 38.71/38.97         <= (((r2_hidden @ sk_B @ sk_C)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['94', '95'])).
% 38.71/38.97  thf('97', plain,
% 38.71/38.97      (((r2_hidden @ sk_B @ sk_C)) | 
% 38.71/38.97       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 38.71/38.97      inference('split', [status(esa)], ['91'])).
% 38.71/38.97  thf('98', plain, (((r2_hidden @ sk_B @ sk_C))),
% 38.71/38.97      inference('sat_resolution*', [status(thm)], ['44', '54', '55', '97'])).
% 38.71/38.97  thf('99', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         ((r2_hidden @ sk_B @ X0)
% 38.71/38.97          | (r2_hidden @ sk_B @ X1)
% 38.71/38.97          | (r2_hidden @ sk_B @ (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ X0) @ X1)))),
% 38.71/38.97      inference('simpl_trail', [status(thm)], ['96', '98'])).
% 38.71/38.97  thf('100', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 38.71/38.97         (~ (r2_hidden @ X3 @ (k4_xboole_0 @ X1 @ X0))
% 38.71/38.97          | ~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ X1)))),
% 38.71/38.97      inference('sup-', [status(thm)], ['66', '67'])).
% 38.71/38.97  thf('101', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.71/38.97         ((r2_hidden @ sk_B @ X0)
% 38.71/38.97          | (r2_hidden @ sk_B @ X1)
% 38.71/38.97          | ~ (r2_hidden @ sk_B @ 
% 38.71/38.97               (k4_xboole_0 @ X2 @ (k4_xboole_0 @ sk_C @ X1))))),
% 38.71/38.97      inference('sup-', [status(thm)], ['99', '100'])).
% 38.71/38.97  thf('102', plain,
% 38.71/38.97      (![X0 : $i, X1 : $i]:
% 38.71/38.97         (~ (r2_hidden @ sk_B @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ sk_C @ X0)))
% 38.71/38.97          | (r2_hidden @ sk_B @ X0))),
% 38.71/38.97      inference('condensation', [status(thm)], ['101'])).
% 38.71/38.97  thf('103', plain,
% 38.71/38.97      (![X0 : $i]:
% 38.71/38.97         (~ (r2_hidden @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))
% 38.71/38.97          | (r2_hidden @ sk_B @ k1_xboole_0))),
% 38.71/38.97      inference('sup-', [status(thm)], ['90', '102'])).
% 38.71/38.97  thf('104', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 38.71/38.97      inference('condensation', [status(thm)], ['4'])).
% 38.71/38.97  thf('105', plain,
% 38.71/38.97      (![X0 : $i]: ~ (r2_hidden @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))),
% 38.71/38.97      inference('clc', [status(thm)], ['103', '104'])).
% 38.71/38.97  thf('106', plain,
% 38.71/38.97      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 38.71/38.97      inference('sup-', [status(thm)], ['89', '105'])).
% 38.71/38.97  thf('107', plain,
% 38.71/38.97      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_xboole_0)))
% 38.71/38.97         <= (~
% 38.71/38.97             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 38.71/38.97      inference('split', [status(esa)], ['42'])).
% 38.71/38.97  thf('108', plain,
% 38.71/38.97      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 38.71/38.97      inference('sat_resolution*', [status(thm)], ['44', '54', '55'])).
% 38.71/38.97  thf('109', plain,
% 38.71/38.97      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_xboole_0))),
% 38.71/38.97      inference('simpl_trail', [status(thm)], ['107', '108'])).
% 38.71/38.97  thf('110', plain, ($false),
% 38.71/38.97      inference('simplify_reflect-', [status(thm)], ['106', '109'])).
% 38.71/38.97  
% 38.71/38.97  % SZS output end Refutation
% 38.71/38.97  
% 38.84/38.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
