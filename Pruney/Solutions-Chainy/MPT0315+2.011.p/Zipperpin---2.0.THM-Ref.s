%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jYSWPNWTBr

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:16 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 197 expanded)
%              Number of leaves         :   19 (  70 expanded)
%              Depth                    :   16
%              Number of atoms          :  563 (1540 expanded)
%              Number of equality atoms :   41 ( 128 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t127_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_xboole_0 @ A @ B )
          | ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t127_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['1'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ sk_C_1 @ sk_D )
      = sk_C_1 )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ sk_C_1 @ sk_C_1 )
      = ( k3_xboole_0 @ sk_C_1 @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C_1 @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['6','13'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X14 @ X16 ) @ ( k3_xboole_0 @ X15 @ X17 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('21',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X14 @ X16 ) @ ( k3_xboole_0 @ X15 @ X17 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('30',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C_1 @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('32',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('33',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('34',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','30','31','32','33'])).

thf('35',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('41',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('43',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('47',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('48',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('49',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','45','46','47','48'])).

thf('50',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('53',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['34','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jYSWPNWTBr
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:34:37 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 278 iterations in 0.148s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.59  thf(t127_zfmisc_1, conjecture,
% 0.41/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.59     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.41/0.59       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.59        ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.41/0.59          ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t127_zfmisc_1])).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ 
% 0.41/0.59          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      (((r1_xboole_0 @ sk_A @ sk_B) | (r1_xboole_0 @ sk_C_1 @ sk_D))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (((r1_xboole_0 @ sk_C_1 @ sk_D)) <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.41/0.59      inference('split', [status(esa)], ['1'])).
% 0.41/0.59  thf(t83_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (![X8 : $i, X9 : $i]:
% 0.41/0.59         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.41/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      ((((k4_xboole_0 @ sk_C_1 @ sk_D) = (sk_C_1)))
% 0.41/0.59         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.59  thf(t48_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X5 : $i, X6 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.41/0.59           = (k3_xboole_0 @ X5 @ X6))),
% 0.41/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      ((((k4_xboole_0 @ sk_C_1 @ sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_D)))
% 0.41/0.59         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.41/0.59  thf('7', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.41/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      (![X8 : $i, X9 : $i]:
% 0.41/0.59         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.41/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.59  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      (![X5 : $i, X6 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.41/0.59           = (k3_xboole_0 @ X5 @ X6))),
% 0.41/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.41/0.59  thf(t2_boole, axiom,
% 0.41/0.59    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.41/0.59  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['11', '12'])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      ((((k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_D)))
% 0.41/0.59         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.41/0.59      inference('demod', [status(thm)], ['6', '13'])).
% 0.41/0.59  thf(t123_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.59     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.41/0.59       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.59         ((k2_zfmisc_1 @ (k3_xboole_0 @ X14 @ X16) @ (k3_xboole_0 @ X15 @ X17))
% 0.41/0.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ X14 @ X15) @ 
% 0.41/0.59              (k2_zfmisc_1 @ X16 @ X17)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.41/0.59  thf(t4_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.41/0.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r1_xboole_0 @ X0 @ X1)
% 0.41/0.59          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.41/0.59  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['11', '12'])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X5 : $i, X6 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.41/0.59           = (k3_xboole_0 @ X5 @ X6))),
% 0.41/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['17', '18'])).
% 0.41/0.59  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.59  thf('21', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.41/0.59      inference('demod', [status(thm)], ['19', '20'])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.41/0.59          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.41/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r1_xboole_0 @ X1 @ X0)
% 0.41/0.59          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['16', '23'])).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.59         (~ (r1_xboole_0 @ 
% 0.41/0.59             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.41/0.59             (k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.41/0.59          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['15', '24'])).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.59         ((k2_zfmisc_1 @ (k3_xboole_0 @ X14 @ X16) @ (k3_xboole_0 @ X15 @ X17))
% 0.41/0.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ X14 @ X15) @ 
% 0.41/0.59              (k2_zfmisc_1 @ X16 @ X17)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.59         (~ (r1_xboole_0 @ 
% 0.41/0.59             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.41/0.59             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 0.41/0.59          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['25', '26'])).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      ((![X0 : $i, X1 : $i]:
% 0.41/0.59          (~ (r1_xboole_0 @ 
% 0.41/0.59              (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0) @ 
% 0.41/0.59              (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.41/0.59               (k3_xboole_0 @ sk_C_1 @ sk_D)))
% 0.41/0.59           | (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C_1) @ 
% 0.41/0.59              (k2_zfmisc_1 @ X0 @ sk_D))))
% 0.41/0.59         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['14', '27'])).
% 0.41/0.59  thf(t113_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.41/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i]:
% 0.41/0.59         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 0.41/0.59          | ((X13) != (k1_xboole_0)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['29'])).
% 0.41/0.59  thf('31', plain,
% 0.41/0.59      ((((k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_D)))
% 0.41/0.59         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.41/0.59      inference('demod', [status(thm)], ['6', '13'])).
% 0.41/0.59  thf('32', plain,
% 0.41/0.59      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['29'])).
% 0.41/0.59  thf('33', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.41/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.41/0.59  thf('34', plain,
% 0.41/0.59      ((![X0 : $i, X1 : $i]:
% 0.41/0.59          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C_1) @ 
% 0.41/0.59           (k2_zfmisc_1 @ X0 @ sk_D)))
% 0.41/0.59         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.41/0.59      inference('demod', [status(thm)], ['28', '30', '31', '32', '33'])).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('split', [status(esa)], ['1'])).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      (![X8 : $i, X9 : $i]:
% 0.41/0.59         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.41/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.59  thf('37', plain,
% 0.41/0.59      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 0.41/0.59         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.59  thf('38', plain,
% 0.41/0.59      (![X5 : $i, X6 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.41/0.59           = (k3_xboole_0 @ X5 @ X6))),
% 0.41/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.59  thf('39', plain,
% 0.41/0.59      ((((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_B)))
% 0.41/0.59         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['37', '38'])).
% 0.41/0.59  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['11', '12'])).
% 0.41/0.59  thf('41', plain,
% 0.41/0.59      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B)))
% 0.41/0.59         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['39', '40'])).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.59         (~ (r1_xboole_0 @ 
% 0.41/0.59             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.41/0.59             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 0.41/0.59          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['25', '26'])).
% 0.41/0.59  thf('43', plain,
% 0.41/0.59      ((![X0 : $i, X1 : $i]:
% 0.41/0.59          (~ (r1_xboole_0 @ 
% 0.41/0.59              (k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.41/0.59              (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.41/0.59               (k3_xboole_0 @ X1 @ X0)))
% 0.41/0.59           | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ 
% 0.41/0.59              (k2_zfmisc_1 @ sk_B @ X0))))
% 0.41/0.59         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.59  thf('44', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i]:
% 0.41/0.59         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 0.41/0.59          | ((X12) != (k1_xboole_0)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.41/0.59  thf('45', plain,
% 0.41/0.59      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['44'])).
% 0.41/0.59  thf('46', plain,
% 0.41/0.59      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B)))
% 0.41/0.59         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['39', '40'])).
% 0.41/0.59  thf('47', plain,
% 0.41/0.59      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['44'])).
% 0.41/0.59  thf('48', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.41/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.41/0.59  thf('49', plain,
% 0.41/0.59      ((![X0 : $i, X1 : $i]:
% 0.41/0.59          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.41/0.59         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['43', '45', '46', '47', '48'])).
% 0.41/0.59  thf('50', plain,
% 0.41/0.59      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ 
% 0.41/0.59          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('51', plain, (~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.59      inference('sup-', [status(thm)], ['49', '50'])).
% 0.41/0.59  thf('52', plain,
% 0.41/0.59      (((r1_xboole_0 @ sk_C_1 @ sk_D)) | ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.59      inference('split', [status(esa)], ['1'])).
% 0.41/0.59  thf('53', plain, (((r1_xboole_0 @ sk_C_1 @ sk_D))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.41/0.59  thf('54', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C_1) @ (k2_zfmisc_1 @ X0 @ sk_D))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['34', '53'])).
% 0.41/0.59  thf('55', plain, ($false), inference('demod', [status(thm)], ['0', '54'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
