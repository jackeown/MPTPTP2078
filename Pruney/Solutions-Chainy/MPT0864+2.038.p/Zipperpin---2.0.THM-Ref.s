%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MchWPzq9hi

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:04 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   91 (1445 expanded)
%              Number of leaves         :   19 ( 385 expanded)
%              Depth                    :   22
%              Number of atoms          :  602 (13398 expanded)
%              Number of equality atoms :  108 (2582 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15 != X14 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X14 ) )
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('1',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X14 ) )
     != ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('4',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('12',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( r2_hidden @ X25 @ X23 )
      | ( ( sk_B @ X23 )
       != ( k4_tarski @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k4_tarski @ X2 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_C_1 ) )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','19','20'])).

thf('22',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X20: $i,X22: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X20 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('24',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('26',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('30',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ( ( sk_B @ X23 )
       != ( k4_tarski @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k4_tarski @ X2 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ ( k4_tarski @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('35',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('41',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['2','3'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_B_1 @ X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('47',plain,
    ( ! [X0: $i] : ( sk_B_1 = X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X0: $i] : ( sk_B_1 = X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('49',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X14 ) )
     != ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('51',plain,
    ( ! [X0: $i,X1: $i] :
        ( X0
       != ( k1_tarski @ X1 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('54',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['21','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('57',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('61',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('62',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('65',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('67',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('68',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('69',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['1','65','66','67','68'])).

thf('70',plain,(
    $false ),
    inference(simplify,[status(thm)],['69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MchWPzq9hi
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 191 iterations in 0.120s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.57  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.37/0.57  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.37/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.57  thf(t20_zfmisc_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.57         ( k1_tarski @ A ) ) <=>
% 0.37/0.57       ( ( A ) != ( B ) ) ))).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      (![X14 : $i, X15 : $i]:
% 0.37/0.57         (((X15) != (X14))
% 0.37/0.57          | ((k4_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X14))
% 0.37/0.57              != (k1_tarski @ X15)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (![X14 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X14))
% 0.37/0.57           != (k1_tarski @ X14))),
% 0.37/0.57      inference('simplify', [status(thm)], ['0'])).
% 0.37/0.57  thf(t20_mcart_1, conjecture,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.37/0.57       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i]:
% 0.37/0.57        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.37/0.57          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.37/0.57  thf('2', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t7_mcart_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.37/0.57       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]: ((k1_mcart_1 @ (k4_tarski @ X20 @ X21)) = (X20))),
% 0.37/0.57      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.37/0.57  thf('4', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.37/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('split', [status(esa)], ['5'])).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['4', '6'])).
% 0.37/0.57  thf('8', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_1)))
% 0.37/0.57         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.57  thf(t9_mcart_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.57          ( ![B:$i]:
% 0.37/0.57            ( ~( ( r2_hidden @ B @ A ) & 
% 0.37/0.57                 ( ![C:$i,D:$i]:
% 0.37/0.57                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.37/0.57                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X23 : $i]:
% 0.37/0.57         (((X23) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X23) @ X23))),
% 0.37/0.57      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.37/0.57  thf(d1_tarski, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (![X0 : $i, X3 : $i]:
% 0.37/0.57         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.37/0.57          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['10', '12'])).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.57         (((X23) = (k1_xboole_0))
% 0.37/0.57          | ~ (r2_hidden @ X25 @ X23)
% 0.37/0.57          | ((sk_B @ X23) != (k4_tarski @ X25 @ X24)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (((X0) != (k4_tarski @ X2 @ X1))
% 0.37/0.57          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.37/0.57          | ~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.37/0.57          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X2 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 0.37/0.57          | ((k1_tarski @ (k4_tarski @ X2 @ X1)) = (k1_xboole_0)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['15'])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.37/0.57         | ((k1_tarski @ (k4_tarski @ sk_A @ sk_C_1)) = (k1_xboole_0))))
% 0.37/0.57         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['9', '16'])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.57  thf('19', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_1)))
% 0.37/0.57         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.37/0.57         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('demod', [status(thm)], ['17', '19', '20'])).
% 0.37/0.57  thf('22', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (![X20 : $i, X22 : $i]: ((k2_mcart_1 @ (k4_tarski @ X20 @ X22)) = (X22))),
% 0.37/0.57      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.37/0.57  thf('24', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 0.37/0.57      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('split', [status(esa)], ['5'])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.37/0.57  thf('27', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.37/0.57         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['26', '27'])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.37/0.57          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['10', '12'])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.57         (((X23) = (k1_xboole_0))
% 0.37/0.57          | ~ (r2_hidden @ X24 @ X23)
% 0.37/0.57          | ((sk_B @ X23) != (k4_tarski @ X25 @ X24)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (((X0) != (k4_tarski @ X2 @ X1))
% 0.37/0.57          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.37/0.57          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.37/0.57          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (![X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 0.37/0.57          | ((k1_tarski @ (k4_tarski @ X2 @ X1)) = (k1_xboole_0)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['31'])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      (((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.37/0.57         | ((k1_tarski @ (k4_tarski @ sk_B_1 @ sk_A)) = (k1_xboole_0))))
% 0.37/0.57         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['28', '32'])).
% 0.37/0.57  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.37/0.57         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['26', '27'])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.37/0.57         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.37/0.57  thf('37', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.57  thf('38', plain,
% 0.37/0.57      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['36', '37'])).
% 0.37/0.57  thf(t113_zfmisc_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.37/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      (![X12 : $i, X13 : $i]:
% 0.37/0.57         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 0.37/0.57          | ((X13) != (k1_xboole_0)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['39'])).
% 0.37/0.57  thf(t10_mcart_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.37/0.57       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.37/0.57         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.57         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 0.37/0.57          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.37/0.57          | (r2_hidden @ (k1_mcart_1 @ X1) @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.57  thf('43', plain,
% 0.37/0.57      ((![X0 : $i]: (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))
% 0.37/0.57         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['38', '42'])).
% 0.37/0.57  thf('44', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.37/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.57  thf('45', plain,
% 0.37/0.57      ((![X0 : $i]: (r2_hidden @ sk_B_1 @ X0))
% 0.37/0.57         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.37/0.57  thf('46', plain,
% 0.37/0.57      (![X0 : $i, X3 : $i]:
% 0.37/0.57         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.57  thf('47', plain,
% 0.37/0.57      ((![X0 : $i]: ((sk_B_1) = (X0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.57  thf('48', plain,
% 0.37/0.57      ((![X0 : $i]: ((sk_B_1) = (X0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.57  thf('49', plain,
% 0.37/0.57      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 0.37/0.57         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['47', '48'])).
% 0.37/0.57  thf('50', plain,
% 0.37/0.57      (![X14 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X14))
% 0.37/0.57           != (k1_tarski @ X14))),
% 0.37/0.57      inference('simplify', [status(thm)], ['0'])).
% 0.37/0.57  thf('51', plain,
% 0.37/0.57      ((![X0 : $i, X1 : $i]: ((X0) != (k1_tarski @ X1)))
% 0.37/0.57         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.57  thf('52', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['51'])).
% 0.37/0.57  thf('53', plain,
% 0.37/0.57      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['5'])).
% 0.37/0.57  thf('54', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 0.37/0.57  thf('55', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.37/0.57      inference('simpl_trail', [status(thm)], ['21', '54'])).
% 0.37/0.57  thf('56', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.57  thf('57', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.37/0.57      inference('sup+', [status(thm)], ['55', '56'])).
% 0.37/0.57  thf('58', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.37/0.57          | (r2_hidden @ (k1_mcart_1 @ X1) @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.57  thf('59', plain, (![X0 : $i]: (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)),
% 0.37/0.57      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.57  thf('60', plain,
% 0.37/0.57      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.57      inference('split', [status(esa)], ['5'])).
% 0.37/0.57  thf('61', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 0.37/0.57  thf('62', plain, (((sk_A) = (k1_mcart_1 @ sk_A))),
% 0.37/0.57      inference('simpl_trail', [status(thm)], ['60', '61'])).
% 0.37/0.57  thf('63', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.37/0.57      inference('demod', [status(thm)], ['59', '62'])).
% 0.37/0.57  thf('64', plain,
% 0.37/0.57      (![X0 : $i, X3 : $i]:
% 0.37/0.57         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.57  thf('65', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['63', '64'])).
% 0.37/0.57  thf('66', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['63', '64'])).
% 0.37/0.57  thf('67', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['63', '64'])).
% 0.37/0.57  thf('68', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['63', '64'])).
% 0.37/0.57  thf('69', plain, (((sk_A) != (sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['1', '65', '66', '67', '68'])).
% 0.37/0.57  thf('70', plain, ($false), inference('simplify', [status(thm)], ['69'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
