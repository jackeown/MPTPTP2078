%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rLT7un2XRU

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:38 EST 2020

% Result     : Theorem 40.62s
% Output     : Refutation 40.62s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 398 expanded)
%              Number of leaves         :   12 ( 102 expanded)
%              Depth                    :   18
%              Number of atoms          : 1257 (4355 expanded)
%              Number of equality atoms :   90 ( 337 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
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
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
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
    ! [X10: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ( X14 = X13 )
      | ( X14 = X10 )
      | ( X12
       != ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('13',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X14 = X10 )
      | ( X14 = X13 )
      | ~ ( r2_hidden @ X14 @ ( k2_tarski @ X13 @ X10 ) ) ) ),
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

thf('32',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X13 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('34',plain,(
    ! [X10: $i,X13: $i] :
      ( r2_hidden @ X13 @ ( k2_tarski @ X13 @ X10 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( r2_hidden @ sk_A @ k1_xboole_0 )
      | ( r2_hidden @ sk_A @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('39',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X10 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('45',plain,(
    ! [X10: $i,X13: $i] :
      ( r2_hidden @ X10 @ ( k2_tarski @ X13 @ X10 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( r2_hidden @ sk_B @ k1_xboole_0 )
      | ( r2_hidden @ sk_B @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('50',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['40'])).

thf('52',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['40'])).

thf('54',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('55',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['42','52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(simpl_trail,[status(thm)],['31','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ X1 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

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

thf('95',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['91'])).

thf('96',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['42','52','53','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(simpl_trail,[status(thm)],['94','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ X1 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

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
    inference(split,[status(esa)],['40'])).

thf('108',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['42','52','53'])).

thf('109',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['106','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rLT7un2XRU
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 40.62/40.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 40.62/40.84  % Solved by: fo/fo7.sh
% 40.62/40.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 40.62/40.84  % done 28605 iterations in 40.405s
% 40.62/40.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 40.62/40.84  % SZS output start Refutation
% 40.62/40.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 40.62/40.84  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 40.62/40.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 40.62/40.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 40.62/40.84  thf(sk_A_type, type, sk_A: $i).
% 40.62/40.84  thf(sk_C_type, type, sk_C: $i).
% 40.62/40.84  thf(sk_B_type, type, sk_B: $i).
% 40.62/40.84  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 40.62/40.84  thf(d5_xboole_0, axiom,
% 40.62/40.84    (![A:$i,B:$i,C:$i]:
% 40.62/40.84     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 40.62/40.84       ( ![D:$i]:
% 40.62/40.84         ( ( r2_hidden @ D @ C ) <=>
% 40.62/40.84           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 40.62/40.84  thf('0', plain,
% 40.62/40.84      (![X1 : $i, X2 : $i, X5 : $i]:
% 40.62/40.84         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 40.62/40.84          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 40.62/40.84          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 40.62/40.84      inference('cnf', [status(esa)], [d5_xboole_0])).
% 40.62/40.84  thf(t4_boole, axiom,
% 40.62/40.84    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 40.62/40.84  thf('1', plain,
% 40.62/40.84      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 40.62/40.84      inference('cnf', [status(esa)], [t4_boole])).
% 40.62/40.84  thf('2', plain,
% 40.62/40.84      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 40.62/40.84         (~ (r2_hidden @ X4 @ X3)
% 40.62/40.84          | ~ (r2_hidden @ X4 @ X2)
% 40.62/40.84          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 40.62/40.84      inference('cnf', [status(esa)], [d5_xboole_0])).
% 40.62/40.84  thf('3', plain,
% 40.62/40.84      (![X1 : $i, X2 : $i, X4 : $i]:
% 40.62/40.84         (~ (r2_hidden @ X4 @ X2)
% 40.62/40.84          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 40.62/40.84      inference('simplify', [status(thm)], ['2'])).
% 40.62/40.84  thf('4', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 40.62/40.84      inference('sup-', [status(thm)], ['1', '3'])).
% 40.62/40.84  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 40.62/40.84      inference('condensation', [status(thm)], ['4'])).
% 40.62/40.84  thf('6', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 40.62/40.84          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['0', '5'])).
% 40.62/40.84  thf('7', plain,
% 40.62/40.84      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 40.62/40.84      inference('cnf', [status(esa)], [t4_boole])).
% 40.62/40.84  thf('8', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 40.62/40.84          | ((X1) = (k1_xboole_0)))),
% 40.62/40.84      inference('demod', [status(thm)], ['6', '7'])).
% 40.62/40.84  thf('9', plain,
% 40.62/40.84      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 40.62/40.84         (~ (r2_hidden @ X4 @ X3)
% 40.62/40.84          | (r2_hidden @ X4 @ X1)
% 40.62/40.84          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 40.62/40.84      inference('cnf', [status(esa)], [d5_xboole_0])).
% 40.62/40.84  thf('10', plain,
% 40.62/40.84      (![X1 : $i, X2 : $i, X4 : $i]:
% 40.62/40.84         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 40.62/40.84      inference('simplify', [status(thm)], ['9'])).
% 40.62/40.84  thf('11', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.62/40.84         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 40.62/40.84          | (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 40.62/40.84             X1))),
% 40.62/40.84      inference('sup-', [status(thm)], ['8', '10'])).
% 40.62/40.84  thf(d2_tarski, axiom,
% 40.62/40.84    (![A:$i,B:$i,C:$i]:
% 40.62/40.84     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 40.62/40.84       ( ![D:$i]:
% 40.62/40.84         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 40.62/40.84  thf('12', plain,
% 40.62/40.84      (![X10 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 40.62/40.84         (~ (r2_hidden @ X14 @ X12)
% 40.62/40.84          | ((X14) = (X13))
% 40.62/40.84          | ((X14) = (X10))
% 40.62/40.84          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 40.62/40.84      inference('cnf', [status(esa)], [d2_tarski])).
% 40.62/40.84  thf('13', plain,
% 40.62/40.84      (![X10 : $i, X13 : $i, X14 : $i]:
% 40.62/40.84         (((X14) = (X10))
% 40.62/40.84          | ((X14) = (X13))
% 40.62/40.84          | ~ (r2_hidden @ X14 @ (k2_tarski @ X13 @ X10)))),
% 40.62/40.84      inference('simplify', [status(thm)], ['12'])).
% 40.62/40.84  thf('14', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 40.62/40.84         (((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3) = (k1_xboole_0))
% 40.62/40.84          | ((sk_D @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3) @ X2 @ 
% 40.62/40.84              k1_xboole_0) = (X1))
% 40.62/40.84          | ((sk_D @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3) @ X2 @ 
% 40.62/40.84              k1_xboole_0) = (X0)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['11', '13'])).
% 40.62/40.84  thf('15', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 40.62/40.84          | ((X1) = (k1_xboole_0)))),
% 40.62/40.84      inference('demod', [status(thm)], ['6', '7'])).
% 40.62/40.84  thf('16', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 40.62/40.84         ((r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1))
% 40.62/40.84          | ((sk_D @ (k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1) @ X3 @ 
% 40.62/40.84              k1_xboole_0) = (X2))
% 40.62/40.84          | ((k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1) = (k1_xboole_0))
% 40.62/40.84          | ((k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1) = (k1_xboole_0)))),
% 40.62/40.84      inference('sup+', [status(thm)], ['14', '15'])).
% 40.62/40.84  thf('17', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 40.62/40.84         (((k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1) = (k1_xboole_0))
% 40.62/40.84          | ((sk_D @ (k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1) @ X3 @ 
% 40.62/40.84              k1_xboole_0) = (X2))
% 40.62/40.84          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1)))),
% 40.62/40.84      inference('simplify', [status(thm)], ['16'])).
% 40.62/40.84  thf('18', plain,
% 40.62/40.84      (![X1 : $i, X2 : $i, X5 : $i]:
% 40.62/40.84         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 40.62/40.84          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 40.62/40.84          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 40.62/40.84      inference('cnf', [status(esa)], [d5_xboole_0])).
% 40.62/40.84  thf('19', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 40.62/40.84          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 40.62/40.84      inference('eq_fact', [status(thm)], ['18'])).
% 40.62/40.84  thf('20', plain,
% 40.62/40.84      (![X1 : $i, X2 : $i, X5 : $i]:
% 40.62/40.84         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 40.62/40.84          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 40.62/40.84          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 40.62/40.84          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 40.62/40.84      inference('cnf', [status(esa)], [d5_xboole_0])).
% 40.62/40.84  thf('21', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 40.62/40.84          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 40.62/40.84          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 40.62/40.84          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['19', '20'])).
% 40.62/40.84  thf('22', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 40.62/40.84          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 40.62/40.84          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 40.62/40.84      inference('simplify', [status(thm)], ['21'])).
% 40.62/40.84  thf('23', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 40.62/40.84          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 40.62/40.84      inference('eq_fact', [status(thm)], ['18'])).
% 40.62/40.84  thf('24', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 40.62/40.84          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 40.62/40.84      inference('clc', [status(thm)], ['22', '23'])).
% 40.62/40.84  thf('25', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 40.62/40.84      inference('condensation', [status(thm)], ['4'])).
% 40.62/40.84  thf('26', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 40.62/40.84      inference('sup-', [status(thm)], ['24', '25'])).
% 40.62/40.84  thf(t73_zfmisc_1, conjecture,
% 40.62/40.84    (![A:$i,B:$i,C:$i]:
% 40.62/40.84     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 40.62/40.84       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 40.62/40.84  thf(zf_stmt_0, negated_conjecture,
% 40.62/40.84    (~( ![A:$i,B:$i,C:$i]:
% 40.62/40.84        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 40.62/40.84          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 40.62/40.84    inference('cnf.neg', [status(esa)], [t73_zfmisc_1])).
% 40.62/40.84  thf('27', plain,
% 40.62/40.84      (((r2_hidden @ sk_A @ sk_C)
% 40.62/40.84        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 40.62/40.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.62/40.84  thf('28', plain,
% 40.62/40.84      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 40.62/40.84      inference('split', [status(esa)], ['27'])).
% 40.62/40.84  thf('29', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 40.62/40.84         (~ (r2_hidden @ X0 @ X1)
% 40.62/40.84          | (r2_hidden @ X0 @ X2)
% 40.62/40.84          | (r2_hidden @ X0 @ X3)
% 40.62/40.84          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 40.62/40.84      inference('cnf', [status(esa)], [d5_xboole_0])).
% 40.62/40.84  thf('30', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.62/40.84         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 40.62/40.84          | (r2_hidden @ X0 @ X2)
% 40.62/40.84          | ~ (r2_hidden @ X0 @ X1))),
% 40.62/40.84      inference('simplify', [status(thm)], ['29'])).
% 40.62/40.84  thf('31', plain,
% 40.62/40.84      ((![X0 : $i]:
% 40.62/40.84          ((r2_hidden @ sk_A @ X0)
% 40.62/40.84           | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_C @ X0))))
% 40.62/40.84         <= (((r2_hidden @ sk_A @ sk_C)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['28', '30'])).
% 40.62/40.84  thf('32', plain,
% 40.62/40.84      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))
% 40.62/40.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 40.62/40.84      inference('split', [status(esa)], ['27'])).
% 40.62/40.84  thf('33', plain,
% 40.62/40.84      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 40.62/40.84         (((X11) != (X13))
% 40.62/40.84          | (r2_hidden @ X11 @ X12)
% 40.62/40.84          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 40.62/40.84      inference('cnf', [status(esa)], [d2_tarski])).
% 40.62/40.84  thf('34', plain,
% 40.62/40.84      (![X10 : $i, X13 : $i]: (r2_hidden @ X13 @ (k2_tarski @ X13 @ X10))),
% 40.62/40.84      inference('simplify', [status(thm)], ['33'])).
% 40.62/40.84  thf('35', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.62/40.84         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 40.62/40.84          | (r2_hidden @ X0 @ X2)
% 40.62/40.84          | ~ (r2_hidden @ X0 @ X1))),
% 40.62/40.84      inference('simplify', [status(thm)], ['29'])).
% 40.62/40.84  thf('36', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.62/40.84         ((r2_hidden @ X1 @ X2)
% 40.62/40.84          | (r2_hidden @ X1 @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['34', '35'])).
% 40.62/40.84  thf('37', plain,
% 40.62/40.84      ((((r2_hidden @ sk_A @ k1_xboole_0) | (r2_hidden @ sk_A @ sk_C)))
% 40.62/40.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 40.62/40.84      inference('sup+', [status(thm)], ['32', '36'])).
% 40.62/40.84  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 40.62/40.84      inference('condensation', [status(thm)], ['4'])).
% 40.62/40.84  thf('39', plain,
% 40.62/40.84      (((r2_hidden @ sk_A @ sk_C))
% 40.62/40.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 40.62/40.84      inference('clc', [status(thm)], ['37', '38'])).
% 40.62/40.84  thf('40', plain,
% 40.62/40.84      ((~ (r2_hidden @ sk_B @ sk_C)
% 40.62/40.84        | ~ (r2_hidden @ sk_A @ sk_C)
% 40.62/40.84        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_xboole_0)))),
% 40.62/40.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.62/40.84  thf('41', plain,
% 40.62/40.84      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 40.62/40.84      inference('split', [status(esa)], ['40'])).
% 40.62/40.84  thf('42', plain,
% 40.62/40.84      (((r2_hidden @ sk_A @ sk_C)) | 
% 40.62/40.84       ~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['39', '41'])).
% 40.62/40.84  thf('43', plain,
% 40.62/40.84      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))
% 40.62/40.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 40.62/40.84      inference('split', [status(esa)], ['27'])).
% 40.62/40.84  thf('44', plain,
% 40.62/40.84      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 40.62/40.84         (((X11) != (X10))
% 40.62/40.84          | (r2_hidden @ X11 @ X12)
% 40.62/40.84          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 40.62/40.84      inference('cnf', [status(esa)], [d2_tarski])).
% 40.62/40.84  thf('45', plain,
% 40.62/40.84      (![X10 : $i, X13 : $i]: (r2_hidden @ X10 @ (k2_tarski @ X13 @ X10))),
% 40.62/40.84      inference('simplify', [status(thm)], ['44'])).
% 40.62/40.84  thf('46', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.62/40.84         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 40.62/40.84          | (r2_hidden @ X0 @ X2)
% 40.62/40.84          | ~ (r2_hidden @ X0 @ X1))),
% 40.62/40.84      inference('simplify', [status(thm)], ['29'])).
% 40.62/40.84  thf('47', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.62/40.84         ((r2_hidden @ X0 @ X2)
% 40.62/40.84          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['45', '46'])).
% 40.62/40.84  thf('48', plain,
% 40.62/40.84      ((((r2_hidden @ sk_B @ k1_xboole_0) | (r2_hidden @ sk_B @ sk_C)))
% 40.62/40.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 40.62/40.84      inference('sup+', [status(thm)], ['43', '47'])).
% 40.62/40.84  thf('49', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 40.62/40.84      inference('condensation', [status(thm)], ['4'])).
% 40.62/40.84  thf('50', plain,
% 40.62/40.84      (((r2_hidden @ sk_B @ sk_C))
% 40.62/40.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 40.62/40.84      inference('clc', [status(thm)], ['48', '49'])).
% 40.62/40.84  thf('51', plain,
% 40.62/40.84      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 40.62/40.84      inference('split', [status(esa)], ['40'])).
% 40.62/40.84  thf('52', plain,
% 40.62/40.84      (((r2_hidden @ sk_B @ sk_C)) | 
% 40.62/40.84       ~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['50', '51'])).
% 40.62/40.84  thf('53', plain,
% 40.62/40.84      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 40.62/40.84       ~ ((r2_hidden @ sk_A @ sk_C)) | ~ ((r2_hidden @ sk_B @ sk_C))),
% 40.62/40.84      inference('split', [status(esa)], ['40'])).
% 40.62/40.84  thf('54', plain,
% 40.62/40.84      (((r2_hidden @ sk_A @ sk_C)) | 
% 40.62/40.84       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 40.62/40.84      inference('split', [status(esa)], ['27'])).
% 40.62/40.84  thf('55', plain, (((r2_hidden @ sk_A @ sk_C))),
% 40.62/40.84      inference('sat_resolution*', [status(thm)], ['42', '52', '53', '54'])).
% 40.62/40.84  thf('56', plain,
% 40.62/40.84      (![X0 : $i]:
% 40.62/40.84         ((r2_hidden @ sk_A @ X0)
% 40.62/40.84          | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_C @ X0)))),
% 40.62/40.84      inference('simpl_trail', [status(thm)], ['31', '55'])).
% 40.62/40.84  thf('57', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.62/40.84         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 40.62/40.84          | (r2_hidden @ X0 @ X2)
% 40.62/40.84          | ~ (r2_hidden @ X0 @ X1))),
% 40.62/40.84      inference('simplify', [status(thm)], ['29'])).
% 40.62/40.84  thf('58', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         ((r2_hidden @ sk_A @ X0)
% 40.62/40.84          | (r2_hidden @ sk_A @ X1)
% 40.62/40.84          | (r2_hidden @ sk_A @ (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ X0) @ X1)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['56', '57'])).
% 40.62/40.84  thf('59', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 40.62/40.84          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 40.62/40.84      inference('eq_fact', [status(thm)], ['18'])).
% 40.62/40.84  thf('60', plain,
% 40.62/40.84      (![X1 : $i, X2 : $i, X4 : $i]:
% 40.62/40.84         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 40.62/40.84      inference('simplify', [status(thm)], ['9'])).
% 40.62/40.84  thf('61', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.62/40.84         (((k4_xboole_0 @ X1 @ X0)
% 40.62/40.84            = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 40.62/40.84          | (r2_hidden @ 
% 40.62/40.84             (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 40.62/40.84             X1))),
% 40.62/40.84      inference('sup-', [status(thm)], ['59', '60'])).
% 40.62/40.84  thf('62', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 40.62/40.84          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 40.62/40.84      inference('clc', [status(thm)], ['22', '23'])).
% 40.62/40.84  thf('63', plain,
% 40.62/40.84      (![X1 : $i, X2 : $i, X4 : $i]:
% 40.62/40.84         (~ (r2_hidden @ X4 @ X2)
% 40.62/40.84          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 40.62/40.84      inference('simplify', [status(thm)], ['2'])).
% 40.62/40.84  thf('64', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.62/40.84         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 40.62/40.84          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 40.62/40.84      inference('sup-', [status(thm)], ['62', '63'])).
% 40.62/40.84  thf('65', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.62/40.84         (((k4_xboole_0 @ X0 @ X1)
% 40.62/40.84            = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0)))
% 40.62/40.84          | ((k4_xboole_0 @ X0 @ X1)
% 40.62/40.84              = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 40.62/40.84                 (k4_xboole_0 @ X2 @ X0))))),
% 40.62/40.84      inference('sup-', [status(thm)], ['61', '64'])).
% 40.62/40.84  thf('66', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.62/40.84         ((k4_xboole_0 @ X0 @ X1)
% 40.62/40.84           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0)))),
% 40.62/40.84      inference('simplify', [status(thm)], ['65'])).
% 40.62/40.84  thf('67', plain,
% 40.62/40.84      (![X1 : $i, X2 : $i, X4 : $i]:
% 40.62/40.84         (~ (r2_hidden @ X4 @ X2)
% 40.62/40.84          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 40.62/40.84      inference('simplify', [status(thm)], ['2'])).
% 40.62/40.84  thf('68', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 40.62/40.84         (~ (r2_hidden @ X3 @ (k4_xboole_0 @ X1 @ X0))
% 40.62/40.84          | ~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ X1)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['66', '67'])).
% 40.62/40.84  thf('69', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.62/40.84         ((r2_hidden @ sk_A @ X0)
% 40.62/40.84          | (r2_hidden @ sk_A @ X1)
% 40.62/40.84          | ~ (r2_hidden @ sk_A @ 
% 40.62/40.84               (k4_xboole_0 @ X2 @ (k4_xboole_0 @ sk_C @ X1))))),
% 40.62/40.84      inference('sup-', [status(thm)], ['58', '68'])).
% 40.62/40.84  thf('70', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         (~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ sk_C @ X0)))
% 40.62/40.84          | (r2_hidden @ sk_A @ X0))),
% 40.62/40.84      inference('condensation', [status(thm)], ['69'])).
% 40.62/40.84  thf('71', plain,
% 40.62/40.84      (![X0 : $i]:
% 40.62/40.84         (~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 40.62/40.84          | (r2_hidden @ sk_A @ k1_xboole_0))),
% 40.62/40.84      inference('sup-', [status(thm)], ['26', '70'])).
% 40.62/40.84  thf('72', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 40.62/40.84      inference('condensation', [status(thm)], ['4'])).
% 40.62/40.84  thf('73', plain,
% 40.62/40.84      (![X0 : $i]: ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))),
% 40.62/40.84      inference('clc', [status(thm)], ['71', '72'])).
% 40.62/40.84  thf('74', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         (((sk_D @ (k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C) @ X1 @ 
% 40.62/40.84            k1_xboole_0) = (X0))
% 40.62/40.84          | ((k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C) = (k1_xboole_0)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['17', '73'])).
% 40.62/40.84  thf('75', plain,
% 40.62/40.84      (![X1 : $i, X2 : $i, X5 : $i]:
% 40.62/40.84         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 40.62/40.84          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 40.62/40.84          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 40.62/40.84      inference('cnf', [status(esa)], [d5_xboole_0])).
% 40.62/40.84  thf('76', plain,
% 40.62/40.84      (![X1 : $i, X2 : $i, X5 : $i]:
% 40.62/40.84         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 40.62/40.84          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 40.62/40.84          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 40.62/40.84      inference('cnf', [status(esa)], [d5_xboole_0])).
% 40.62/40.84  thf('77', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 40.62/40.84          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 40.62/40.84          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 40.62/40.84          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['75', '76'])).
% 40.62/40.84  thf('78', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 40.62/40.84          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 40.62/40.84      inference('simplify', [status(thm)], ['77'])).
% 40.62/40.84  thf('79', plain,
% 40.62/40.84      (![X1 : $i, X2 : $i, X5 : $i]:
% 40.62/40.84         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 40.62/40.84          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 40.62/40.84          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 40.62/40.84      inference('cnf', [status(esa)], [d5_xboole_0])).
% 40.62/40.84  thf('80', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 40.62/40.84      inference('condensation', [status(thm)], ['4'])).
% 40.62/40.84  thf('81', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 40.62/40.84          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['79', '80'])).
% 40.62/40.84  thf('82', plain,
% 40.62/40.84      (![X1 : $i, X2 : $i, X5 : $i]:
% 40.62/40.84         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 40.62/40.84          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 40.62/40.84          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 40.62/40.84      inference('cnf', [status(esa)], [d5_xboole_0])).
% 40.62/40.84  thf('83', plain,
% 40.62/40.84      (![X0 : $i]:
% 40.62/40.84         (((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))
% 40.62/40.84          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 40.62/40.84          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['81', '82'])).
% 40.62/40.84  thf('84', plain,
% 40.62/40.84      (![X0 : $i]:
% 40.62/40.84         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 40.62/40.84          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 40.62/40.84      inference('simplify', [status(thm)], ['83'])).
% 40.62/40.84  thf('85', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 40.62/40.84      inference('condensation', [status(thm)], ['4'])).
% 40.62/40.84  thf('86', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 40.62/40.84      inference('clc', [status(thm)], ['84', '85'])).
% 40.62/40.84  thf('87', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 40.62/40.84      inference('demod', [status(thm)], ['78', '86'])).
% 40.62/40.84  thf('88', plain,
% 40.62/40.84      (![X0 : $i]:
% 40.62/40.84         ((r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C))
% 40.62/40.84          | ((k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C) = (k1_xboole_0))
% 40.62/40.84          | ((k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C) = (k1_xboole_0)))),
% 40.62/40.84      inference('sup+', [status(thm)], ['74', '87'])).
% 40.62/40.84  thf('89', plain,
% 40.62/40.84      (![X0 : $i]:
% 40.62/40.84         (((k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C) = (k1_xboole_0))
% 40.62/40.84          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C)))),
% 40.62/40.84      inference('simplify', [status(thm)], ['88'])).
% 40.62/40.84  thf('90', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 40.62/40.84      inference('sup-', [status(thm)], ['24', '25'])).
% 40.62/40.84  thf('91', plain,
% 40.62/40.84      (((r2_hidden @ sk_B @ sk_C)
% 40.62/40.84        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 40.62/40.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.62/40.84  thf('92', plain,
% 40.62/40.84      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 40.62/40.84      inference('split', [status(esa)], ['91'])).
% 40.62/40.84  thf('93', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.62/40.84         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 40.62/40.84          | (r2_hidden @ X0 @ X2)
% 40.62/40.84          | ~ (r2_hidden @ X0 @ X1))),
% 40.62/40.84      inference('simplify', [status(thm)], ['29'])).
% 40.62/40.84  thf('94', plain,
% 40.62/40.84      ((![X0 : $i]:
% 40.62/40.84          ((r2_hidden @ sk_B @ X0)
% 40.62/40.84           | (r2_hidden @ sk_B @ (k4_xboole_0 @ sk_C @ X0))))
% 40.62/40.84         <= (((r2_hidden @ sk_B @ sk_C)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['92', '93'])).
% 40.62/40.84  thf('95', plain,
% 40.62/40.84      (((r2_hidden @ sk_B @ sk_C)) | 
% 40.62/40.84       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 40.62/40.84      inference('split', [status(esa)], ['91'])).
% 40.62/40.84  thf('96', plain, (((r2_hidden @ sk_B @ sk_C))),
% 40.62/40.84      inference('sat_resolution*', [status(thm)], ['42', '52', '53', '95'])).
% 40.62/40.84  thf('97', plain,
% 40.62/40.84      (![X0 : $i]:
% 40.62/40.84         ((r2_hidden @ sk_B @ X0)
% 40.62/40.84          | (r2_hidden @ sk_B @ (k4_xboole_0 @ sk_C @ X0)))),
% 40.62/40.84      inference('simpl_trail', [status(thm)], ['94', '96'])).
% 40.62/40.84  thf('98', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.62/40.84         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 40.62/40.84          | (r2_hidden @ X0 @ X2)
% 40.62/40.84          | ~ (r2_hidden @ X0 @ X1))),
% 40.62/40.84      inference('simplify', [status(thm)], ['29'])).
% 40.62/40.84  thf('99', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         ((r2_hidden @ sk_B @ X0)
% 40.62/40.84          | (r2_hidden @ sk_B @ X1)
% 40.62/40.84          | (r2_hidden @ sk_B @ (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ X0) @ X1)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['97', '98'])).
% 40.62/40.84  thf('100', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 40.62/40.84         (~ (r2_hidden @ X3 @ (k4_xboole_0 @ X1 @ X0))
% 40.62/40.84          | ~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ X1)))),
% 40.62/40.84      inference('sup-', [status(thm)], ['66', '67'])).
% 40.62/40.84  thf('101', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.62/40.84         ((r2_hidden @ sk_B @ X0)
% 40.62/40.84          | (r2_hidden @ sk_B @ X1)
% 40.62/40.84          | ~ (r2_hidden @ sk_B @ 
% 40.62/40.84               (k4_xboole_0 @ X2 @ (k4_xboole_0 @ sk_C @ X1))))),
% 40.62/40.84      inference('sup-', [status(thm)], ['99', '100'])).
% 40.62/40.84  thf('102', plain,
% 40.62/40.84      (![X0 : $i, X1 : $i]:
% 40.62/40.84         (~ (r2_hidden @ sk_B @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ sk_C @ X0)))
% 40.62/40.84          | (r2_hidden @ sk_B @ X0))),
% 40.62/40.84      inference('condensation', [status(thm)], ['101'])).
% 40.62/40.84  thf('103', plain,
% 40.62/40.84      (![X0 : $i]:
% 40.62/40.84         (~ (r2_hidden @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))
% 40.62/40.84          | (r2_hidden @ sk_B @ k1_xboole_0))),
% 40.62/40.84      inference('sup-', [status(thm)], ['90', '102'])).
% 40.62/40.84  thf('104', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 40.62/40.84      inference('condensation', [status(thm)], ['4'])).
% 40.62/40.84  thf('105', plain,
% 40.62/40.84      (![X0 : $i]: ~ (r2_hidden @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))),
% 40.62/40.84      inference('clc', [status(thm)], ['103', '104'])).
% 40.62/40.84  thf('106', plain,
% 40.62/40.84      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 40.62/40.84      inference('sup-', [status(thm)], ['89', '105'])).
% 40.62/40.84  thf('107', plain,
% 40.62/40.84      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_xboole_0)))
% 40.62/40.84         <= (~
% 40.62/40.84             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 40.62/40.84      inference('split', [status(esa)], ['40'])).
% 40.62/40.84  thf('108', plain,
% 40.62/40.84      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 40.62/40.84      inference('sat_resolution*', [status(thm)], ['42', '52', '53'])).
% 40.62/40.84  thf('109', plain,
% 40.62/40.84      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_xboole_0))),
% 40.62/40.84      inference('simpl_trail', [status(thm)], ['107', '108'])).
% 40.62/40.84  thf('110', plain, ($false),
% 40.62/40.84      inference('simplify_reflect-', [status(thm)], ['106', '109'])).
% 40.62/40.84  
% 40.62/40.84  % SZS output end Refutation
% 40.62/40.84  
% 40.62/40.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
