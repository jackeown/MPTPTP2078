%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QqoWuyHppx

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 776 expanded)
%              Number of leaves         :   23 ( 241 expanded)
%              Depth                    :   17
%              Number of atoms          :  638 (6775 expanded)
%              Number of equality atoms :  119 (1189 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('0',plain,(
    ! [X55: $i] :
      ( ( X55 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X55 ) @ X55 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X41 ) @ ( k1_tarski @ X42 ) )
        = ( k1_tarski @ X41 ) )
      | ( X41 = X42 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X43 @ X44 )
      | ( ( k4_xboole_0 @ X44 @ ( k1_tarski @ X43 ) )
       != X44 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k4_xboole_0 @ X44 @ ( k1_tarski @ X45 ) )
        = X44 )
      | ( r2_hidden @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X41 != X40 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X41 ) @ ( k1_tarski @ X40 ) )
       != ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('14',plain,(
    ! [X40: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X40 ) @ ( k1_tarski @ X40 ) )
     != ( k1_tarski @ X40 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','18'])).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('20',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('21',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X52 @ X53 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('22',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','24'])).

thf('26',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( X55 = k1_xboole_0 )
      | ~ ( r2_hidden @ X57 @ X55 )
      | ( ( sk_B @ X55 )
       != ( k4_tarski @ X57 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','29'])).

thf('31',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','30'])).

thf('32',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','18'])).

thf('35',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X52: $i,X54: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X52 @ X54 ) )
      = X54 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('37',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('39',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( X55 = k1_xboole_0 )
      | ~ ( r2_hidden @ X56 @ X55 )
      | ( ( sk_B @ X55 )
       != ( k4_tarski @ X57 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('50',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('53',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('54',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50','51','54','55'])).

thf('57',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('59',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['32','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('62',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('64',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['32','59'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('66',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['52','53'])).

thf('67',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['32','59'])).

thf('68',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63','64','65','66','67'])).

thf('69',plain,(
    $false ),
    inference(simplify,[status(thm)],['68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QqoWuyHppx
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:31:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 121 iterations in 0.055s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.52  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.52  thf(t9_mcart_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.52                 ( ![C:$i,D:$i]:
% 0.22/0.52                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.22/0.52                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (![X55 : $i]:
% 0.22/0.52         (((X55) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X55) @ X55))),
% 0.22/0.52      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.52  thf(t20_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.52         ( k1_tarski @ A ) ) <=>
% 0.22/0.52       ( ( A ) != ( B ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X41 : $i, X42 : $i]:
% 0.22/0.52         (((k4_xboole_0 @ (k1_tarski @ X41) @ (k1_tarski @ X42))
% 0.22/0.52            = (k1_tarski @ X41))
% 0.22/0.52          | ((X41) = (X42)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.52  thf(t65_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.22/0.52       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X43 : $i, X44 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X43 @ X44)
% 0.22/0.52          | ((k4_xboole_0 @ X44 @ (k1_tarski @ X43)) != (X44)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.22/0.52          | ((X0) = (X1))
% 0.22/0.52          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.52          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '4'])).
% 0.22/0.52  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.52  thf('6', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.52  thf(t100_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X7 @ X8)
% 0.22/0.52           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X44 : $i, X45 : $i]:
% 0.22/0.52         (((k4_xboole_0 @ X44 @ (k1_tarski @ X45)) = (X44))
% 0.22/0.52          | (r2_hidden @ X45 @ X44))),
% 0.22/0.52      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.22/0.52            = (k1_tarski @ X0))
% 0.22/0.52          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.52  thf(t69_enumset1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X40 : $i, X41 : $i]:
% 0.22/0.52         (((X41) != (X40))
% 0.22/0.52          | ((k4_xboole_0 @ (k1_tarski @ X41) @ (k1_tarski @ X40))
% 0.22/0.52              != (k1_tarski @ X41)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X40 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ (k1_tarski @ X40) @ (k1_tarski @ X40))
% 0.22/0.52           != (k1_tarski @ X40))),
% 0.22/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 0.22/0.52           != (k1_tarski @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.22/0.52           != (k1_tarski @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.22/0.52           != (k1_tarski @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf('19', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['10', '18'])).
% 0.22/0.52  thf(t20_mcart_1, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.52       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.52          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.22/0.52  thf('20', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t7_mcart_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.22/0.52       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X52 : $i, X53 : $i]: ((k1_mcart_1 @ (k4_tarski @ X52 @ X53)) = (X52))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.52  thf('22', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.22/0.52      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('split', [status(esa)], ['23'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('sup+', [status(thm)], ['22', '24'])).
% 0.22/0.52  thf('26', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.22/0.52         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('sup+', [status(thm)], ['25', '26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.22/0.52         (((X55) = (k1_xboole_0))
% 0.22/0.52          | ~ (r2_hidden @ X57 @ X55)
% 0.22/0.52          | ((sk_B @ X55) != (k4_tarski @ X57 @ X56)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (((sk_B @ X0) != (sk_A))
% 0.22/0.52           | ~ (r2_hidden @ sk_A @ X0)
% 0.22/0.52           | ((X0) = (k1_xboole_0))))
% 0.22/0.52         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.52         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.22/0.52         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['19', '29'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (((((sk_A) != (sk_A))
% 0.22/0.52         | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.52         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.52          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '4'])).
% 0.22/0.52  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['10', '18'])).
% 0.22/0.52  thf('35', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X52 : $i, X54 : $i]: ((k2_mcart_1 @ (k4_tarski @ X52 @ X54)) = (X54))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.52  thf('37', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.22/0.52      inference('sup+', [status(thm)], ['35', '36'])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('split', [status(esa)], ['23'])).
% 0.22/0.52  thf('39', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('sup+', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf('40', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.22/0.52         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('sup+', [status(thm)], ['39', '40'])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.22/0.52         (((X55) = (k1_xboole_0))
% 0.22/0.52          | ~ (r2_hidden @ X56 @ X55)
% 0.22/0.52          | ((sk_B @ X55) != (k4_tarski @ X57 @ X56)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (((sk_B @ X0) != (sk_A))
% 0.22/0.52           | ~ (r2_hidden @ sk_A @ X0)
% 0.22/0.52           | ((X0) = (k1_xboole_0))))
% 0.22/0.52         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.52         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.22/0.52         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['34', '43'])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      (((((sk_A) != (sk_A))
% 0.22/0.52         | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.52         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['33', '44'])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['45'])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 0.22/0.52           != (k1_tarski @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '14'])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ k1_xboole_0)
% 0.22/0.52          != (k1_tarski @ sk_A)))
% 0.22/0.52         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['45'])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf(t3_boole, axiom,
% 0.22/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.52  thf('53', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      (((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['52', '53'])).
% 0.22/0.52  thf('55', plain,
% 0.22/0.52      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['45'])).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['48', '49', '50', '51', '54', '55'])).
% 0.22/0.52  thf('57', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['56'])).
% 0.22/0.52  thf('58', plain,
% 0.22/0.52      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['23'])).
% 0.22/0.52  thf('59', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['57', '58'])).
% 0.22/0.52  thf('60', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['32', '59'])).
% 0.22/0.52  thf('61', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 0.22/0.52           != (k1_tarski @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '14'])).
% 0.22/0.52  thf('62', plain,
% 0.22/0.52      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ k1_xboole_0)
% 0.22/0.52         != (k1_tarski @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.22/0.52  thf('63', plain,
% 0.22/0.52      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf('64', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['32', '59'])).
% 0.22/0.52  thf('65', plain,
% 0.22/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('66', plain,
% 0.22/0.52      (((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['52', '53'])).
% 0.22/0.52  thf('67', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['32', '59'])).
% 0.22/0.52  thf('68', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['62', '63', '64', '65', '66', '67'])).
% 0.22/0.52  thf('69', plain, ($false), inference('simplify', [status(thm)], ['68'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
