%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8ZUAgzFG0t

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:46 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 295 expanded)
%              Number of leaves         :   21 (  83 expanded)
%              Depth                    :   21
%              Number of atoms          :  664 (2825 expanded)
%              Number of equality atoms :   90 ( 431 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X48: $i,X49: $i] :
      ( ( X49
        = ( k1_tarski @ X48 ) )
      | ( X49 = k1_xboole_0 )
      | ~ ( r1_tarski @ X49 @ ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('3',plain,
    ( ( sk_A = sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A != sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A != sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X30 != X29 )
      | ( r2_hidden @ X30 @ X31 )
      | ( X31
       != ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X29: $i] :
      ( r2_hidden @ X29 @ ( k1_tarski @ X29 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A = sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A = sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_B_1 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('15',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_B_1 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('19',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_B_1 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('20',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X52 = X51 )
      | ~ ( r1_tarski @ ( k1_tarski @ X52 ) @ ( k1_tarski @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        | ( sk_B_1 = X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ X49 @ ( k1_tarski @ X50 ) )
      | ( X49 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('23',plain,(
    ! [X50: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X50 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ! [X0: $i] : ( sk_B_1 = X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','23'])).

thf('25',plain,
    ( ! [X0: $i] : ( sk_B_1 = X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','23'])).

thf('26',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('31',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( r1_tarski @ X18 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_xboole_0 @ X19 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['32','38'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('41',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','45'])).

thf('47',plain,
    ( ! [X0: $i,X1: $i] :
        ~ ( r2_hidden @ X1 @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','46'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','47'])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('50',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['6','48','49'])).

thf('51',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['4','50'])).

thf('52',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','51'])).

thf('53',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X52 = X51 )
      | ~ ( r1_tarski @ ( k1_tarski @ X52 ) @ ( k1_tarski @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('58',plain,(
    sk_A = sk_B_1 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_A != sk_B_1 )
   <= ( sk_A != sk_B_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('60',plain,(
    sk_A != sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['6','48'])).

thf('61',plain,(
    sk_A != sk_B_1 ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8ZUAgzFG0t
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:38:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 382 iterations in 0.126s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(t36_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.38/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.58  thf(l3_zfmisc_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.38/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X48 : $i, X49 : $i]:
% 0.38/0.58         (((X49) = (k1_tarski @ X48))
% 0.38/0.58          | ((X49) = (k1_xboole_0))
% 0.38/0.58          | ~ (r1_tarski @ X49 @ (k1_tarski @ X48)))),
% 0.38/0.58      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.38/0.58          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.58  thf(t20_zfmisc_1, conjecture,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.58         ( k1_tarski @ A ) ) <=>
% 0.38/0.58       ( ( A ) != ( B ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i,B:$i]:
% 0.38/0.58        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.58            ( k1_tarski @ A ) ) <=>
% 0.38/0.58          ( ( A ) != ( B ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      ((((sk_A) = (sk_B_1))
% 0.38/0.58        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58            != (k1_tarski @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58          != (k1_tarski @ sk_A)))
% 0.38/0.58         <= (~
% 0.38/0.58             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58                = (k1_tarski @ sk_A))))),
% 0.38/0.58      inference('split', [status(esa)], ['3'])).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      ((((sk_A) != (sk_B_1))
% 0.38/0.58        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58            = (k1_tarski @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (~ (((sk_A) = (sk_B_1))) | 
% 0.38/0.58       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58          = (k1_tarski @ sk_A)))),
% 0.38/0.58      inference('split', [status(esa)], ['5'])).
% 0.38/0.58  thf(d1_tarski, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.58         (((X30) != (X29))
% 0.38/0.58          | (r2_hidden @ X30 @ X31)
% 0.38/0.58          | ((X31) != (k1_tarski @ X29)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.58  thf('8', plain, (![X29 : $i]: (r2_hidden @ X29 @ (k1_tarski @ X29))),
% 0.38/0.58      inference('simplify', [status(thm)], ['7'])).
% 0.38/0.58  thf('9', plain, ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (sk_B_1))))),
% 0.38/0.58      inference('split', [status(esa)], ['3'])).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58          = (k1_tarski @ sk_A)))
% 0.38/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58                = (k1_tarski @ sk_A))))),
% 0.38/0.58      inference('split', [status(esa)], ['5'])).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      ((((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1))
% 0.38/0.58          = (k1_tarski @ sk_A)))
% 0.38/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58                = (k1_tarski @ sk_A))) & 
% 0.38/0.58             (((sk_A) = (sk_B_1))))),
% 0.38/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.58  thf('12', plain, ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (sk_B_1))))),
% 0.38/0.58      inference('split', [status(esa)], ['3'])).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      ((((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1))
% 0.38/0.58          = (k1_tarski @ sk_B_1)))
% 0.38/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58                = (k1_tarski @ sk_A))) & 
% 0.38/0.58             (((sk_A) = (sk_B_1))))),
% 0.38/0.58      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.38/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (((r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1)))
% 0.38/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58                = (k1_tarski @ sk_A))) & 
% 0.38/0.58             (((sk_A) = (sk_B_1))))),
% 0.38/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.38/0.58  thf(l32_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (![X11 : $i, X13 : $i]:
% 0.38/0.58         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.38/0.58          | ~ (r1_tarski @ X11 @ X13))),
% 0.38/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      ((((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1))
% 0.38/0.58          = (k1_xboole_0)))
% 0.38/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58                = (k1_tarski @ sk_A))) & 
% 0.38/0.58             (((sk_A) = (sk_B_1))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      ((((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1))
% 0.38/0.58          = (k1_tarski @ sk_B_1)))
% 0.38/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58                = (k1_tarski @ sk_A))) & 
% 0.38/0.58             (((sk_A) = (sk_B_1))))),
% 0.38/0.58      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      ((((k1_xboole_0) = (k1_tarski @ sk_B_1)))
% 0.38/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58                = (k1_tarski @ sk_A))) & 
% 0.38/0.58             (((sk_A) = (sk_B_1))))),
% 0.38/0.58      inference('sup+', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf(t6_zfmisc_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.38/0.58       ( ( A ) = ( B ) ) ))).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X51 : $i, X52 : $i]:
% 0.38/0.58         (((X52) = (X51))
% 0.38/0.58          | ~ (r1_tarski @ (k1_tarski @ X52) @ (k1_tarski @ X51)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      ((![X0 : $i]:
% 0.38/0.58          (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) | ((sk_B_1) = (X0))))
% 0.38/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58                = (k1_tarski @ sk_A))) & 
% 0.38/0.58             (((sk_A) = (sk_B_1))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      (![X49 : $i, X50 : $i]:
% 0.38/0.58         ((r1_tarski @ X49 @ (k1_tarski @ X50)) | ((X49) != (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      (![X50 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X50))),
% 0.38/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      ((![X0 : $i]: ((sk_B_1) = (X0)))
% 0.38/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58                = (k1_tarski @ sk_A))) & 
% 0.38/0.58             (((sk_A) = (sk_B_1))))),
% 0.38/0.58      inference('demod', [status(thm)], ['21', '23'])).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      ((![X0 : $i]: ((sk_B_1) = (X0)))
% 0.38/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58                = (k1_tarski @ sk_A))) & 
% 0.38/0.58             (((sk_A) = (sk_B_1))))),
% 0.38/0.58      inference('demod', [status(thm)], ['21', '23'])).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 0.38/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58                = (k1_tarski @ sk_A))) & 
% 0.38/0.58             (((sk_A) = (sk_B_1))))),
% 0.38/0.58      inference('sup+', [status(thm)], ['24', '25'])).
% 0.38/0.58  thf(t2_boole, axiom,
% 0.38/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.38/0.58  thf(t4_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.38/0.58            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.38/0.58          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.38/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.58  thf(t3_xboole_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.58  thf('31', plain,
% 0.38/0.58      (![X18 : $i]:
% 0.38/0.58         (((X18) = (k1_xboole_0)) | ~ (r1_tarski @ X18 @ k1_xboole_0))),
% 0.38/0.58      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i]:
% 0.38/0.58         ((r1_tarski @ X11 @ X12)
% 0.38/0.58          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.58  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.58      inference('simplify', [status(thm)], ['35'])).
% 0.38/0.58  thf(t85_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.38/0.58  thf('37', plain,
% 0.38/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X19 @ X20)
% 0.38/0.58          | (r1_xboole_0 @ X19 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.38/0.58  thf('38', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (r1_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.58  thf('39', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.38/0.58      inference('sup+', [status(thm)], ['32', '38'])).
% 0.38/0.58  thf(t3_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.38/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.38/0.58            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      (![X2 : $i, X3 : $i]:
% 0.38/0.58         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 0.38/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.58  thf('41', plain,
% 0.38/0.58      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.38/0.58          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.58          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['39', '42'])).
% 0.38/0.58  thf('44', plain,
% 0.38/0.58      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.38/0.58  thf('45', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.38/0.58      inference('demod', [status(thm)], ['43', '44'])).
% 0.38/0.58  thf('46', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.38/0.58      inference('demod', [status(thm)], ['29', '45'])).
% 0.38/0.58  thf('47', plain,
% 0.38/0.58      ((![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ X0))
% 0.38/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58                = (k1_tarski @ sk_A))) & 
% 0.38/0.58             (((sk_A) = (sk_B_1))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['26', '46'])).
% 0.38/0.58  thf('48', plain,
% 0.38/0.58      (~
% 0.38/0.58       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58          = (k1_tarski @ sk_A))) | 
% 0.38/0.58       ~ (((sk_A) = (sk_B_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['8', '47'])).
% 0.38/0.58  thf('49', plain,
% 0.38/0.58      (~
% 0.38/0.58       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58          = (k1_tarski @ sk_A))) | 
% 0.38/0.58       (((sk_A) = (sk_B_1)))),
% 0.38/0.58      inference('split', [status(esa)], ['3'])).
% 0.38/0.58  thf('50', plain,
% 0.38/0.58      (~
% 0.38/0.58       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58          = (k1_tarski @ sk_A)))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['6', '48', '49'])).
% 0.38/0.58  thf('51', plain,
% 0.38/0.58      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58         != (k1_tarski @ sk_A))),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['4', '50'])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.38/0.58        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58            = (k1_xboole_0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['2', '51'])).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.58         = (k1_xboole_0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['52'])).
% 0.38/0.58  thf('54', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i]:
% 0.38/0.58         ((r1_tarski @ X11 @ X12)
% 0.38/0.58          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.58  thf('55', plain,
% 0.38/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.58        | (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.38/0.58  thf('56', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.38/0.58      inference('simplify', [status(thm)], ['55'])).
% 0.38/0.58  thf('57', plain,
% 0.38/0.58      (![X51 : $i, X52 : $i]:
% 0.38/0.58         (((X52) = (X51))
% 0.38/0.58          | ~ (r1_tarski @ (k1_tarski @ X52) @ (k1_tarski @ X51)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.38/0.58  thf('58', plain, (((sk_A) = (sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.58  thf('59', plain, ((((sk_A) != (sk_B_1))) <= (~ (((sk_A) = (sk_B_1))))),
% 0.38/0.58      inference('split', [status(esa)], ['5'])).
% 0.38/0.58  thf('60', plain, (~ (((sk_A) = (sk_B_1)))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['6', '48'])).
% 0.38/0.58  thf('61', plain, (((sk_A) != (sk_B_1))),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.38/0.58  thf('62', plain, ($false),
% 0.38/0.58      inference('simplify_reflect-', [status(thm)], ['58', '61'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
