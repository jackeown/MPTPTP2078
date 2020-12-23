%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vRPdNG7DtR

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 347 expanded)
%              Number of leaves         :   19 (  95 expanded)
%              Depth                    :   17
%              Number of atoms          :  627 (3743 expanded)
%              Number of equality atoms :  112 ( 729 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t130_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != k1_xboole_0 )
       => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
           != k1_xboole_0 )
          & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_zfmisc_1])).

thf('0',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X9 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X9 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('9',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X12 ) )
      | ( X11 = X12 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        | ( X0 = sk_B ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t63_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
     => ( r2_hidden @ A @ C ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X16 @ X18 ) @ X17 )
       != ( k2_tarski @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t63_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
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

thf('24',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ! [X0: $i] : ( X0 = sk_B )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('28',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14 != X13 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X13 ) )
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('30',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X13 ) )
     != ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('33',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ! [X0: $i] : ( X0 = sk_B )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('36',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ! [X0: $i] : ( X0 != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['6','40'])).

thf('42',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t75_zfmisc_1,axiom,(
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

thf('43',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ ( k2_tarski @ X19 @ X22 ) )
        = k1_xboole_0 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t75_zfmisc_1])).

thf('44',plain,(
    ! [X19: $i,X22: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X19 @ X22 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['41','45'])).

thf('47',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('48',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X13 ) )
     != ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('51',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('52',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('54',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vRPdNG7DtR
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:42:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 70 iterations in 0.035s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(t130_zfmisc_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.50       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.50          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf(t113_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         (((X8) = (k1_xboole_0))
% 0.21/0.50          | ((X9) = (k1_xboole_0))
% 0.21/0.50          | ((k2_zfmisc_1 @ X9 @ X8) != (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50         | ((sk_A) = (k1_xboole_0))
% 0.21/0.50         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.50  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         (((X8) = (k1_xboole_0))
% 0.21/0.50          | ((X9) = (k1_xboole_0))
% 0.21/0.50          | ((k2_zfmisc_1 @ X9 @ X8) != (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.50         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.50  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf(t17_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( A ) != ( B ) ) =>
% 0.21/0.50       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X12))
% 0.21/0.50          | ((X11) = (X12)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          ((r1_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) | ((X0) = (sk_B))))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf(t69_enumset1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.50  thf('16', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.50  thf(t2_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.50  thf(t63_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.21/0.50       ( r2_hidden @ A @ C ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.50         ((r2_hidden @ X16 @ X17)
% 0.21/0.50          | ((k3_xboole_0 @ (k2_tarski @ X16 @ X18) @ X17)
% 0.21/0.50              != (k2_tarski @ X16 @ X18)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t63_zfmisc_1])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k1_xboole_0) != (k2_tarski @ X1 @ X0))
% 0.21/0.50          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_xboole_0) != (k1_tarski @ X0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (((((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_B @ k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (((r2_hidden @ sk_B @ k1_xboole_0))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.50  thf(t4_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.50            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.21/0.50          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((![X0 : $i]: ~ (r1_xboole_0 @ X0 @ k1_xboole_0))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      ((![X0 : $i]: ((X0) = (sk_B)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf(t20_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.50         ( k1_tarski @ A ) ) <=>
% 0.21/0.50       ( ( A ) != ( B ) ) ))).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]:
% 0.21/0.50         (((X14) != (X13))
% 0.21/0.50          | ((k4_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X13))
% 0.21/0.50              != (k1_tarski @ X14)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X13 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ (k1_tarski @ X13) @ (k1_tarski @ X13))
% 0.21/0.50           != (k1_tarski @ X13))),
% 0.21/0.50      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['28', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      ((![X0 : $i]: ((X0) = (sk_B)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '26'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((((sk_B) != (k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      ((![X0 : $i]: ((X0) != (k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.21/0.50       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['6', '40'])).
% 0.21/0.50  thf('42', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.50  thf(t75_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.50       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.21/0.50            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.21/0.50         (((k4_xboole_0 @ X21 @ (k2_tarski @ X19 @ X22)) = (k1_xboole_0))
% 0.21/0.50          | ((X21) != (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t75_zfmisc_1])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X19 : $i, X22 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X19 @ X22)) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['42', '44'])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['41', '45'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X13 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ (k1_tarski @ X13) @ (k1_tarski @ X13))
% 0.21/0.50           != (k1_tarski @ X13))),
% 0.21/0.50      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.50         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.21/0.50      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['52', '53'])).
% 0.21/0.50  thf('55', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['46', '54'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
