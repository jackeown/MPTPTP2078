%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nwKxpDIWDl

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:17 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 811 expanded)
%              Number of leaves         :    9 ( 175 expanded)
%              Depth                    :   20
%              Number of atoms          :  729 (12270 expanded)
%              Number of equality atoms :  111 (2151 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t42_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
      <=> ~ ( ( A != k1_xboole_0 )
            & ( A
             != ( k1_tarski @ B ) )
            & ( A
             != ( k1_tarski @ C ) )
            & ( A
             != ( k2_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_zfmisc_1])).

thf('0',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

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

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_tarski @ X0 @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('13',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['9'])).

thf('15',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['7'])).

thf('18',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('21',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('24',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('25',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ ( k2_tarski @ X0 @ X3 ) )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) )
   <= ( ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['24','30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['23','31'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf('34',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['6','8','10','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['4','35'])).

thf('37',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('38',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ ( k2_tarski @ X0 @ X3 ) )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X3: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ X0 ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['6','8','10','34'])).

thf('45',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['43','44'])).

thf('46',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('48',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_C ) )
   <= ( sk_A
      = ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ ( k2_tarski @ X0 @ X3 ) )
      | ( X2
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X3: $i] :
      ( r1_tarski @ ( k1_tarski @ X3 ) @ ( k2_tarski @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_A @ ( k2_tarski @ X0 @ sk_C ) )
   <= ( sk_A
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup+',[status(thm)],['48','50'])).

thf('52',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['43','44'])).

thf('53',plain,(
    sk_A
 != ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( sk_A
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['24','37','46','6','8','10','47','53','54'])).

thf('56',plain,(
    ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['36','55'])).

thf('57',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( sk_A
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['24','37','46','6','8','10','47','53','54'])).

thf('59',plain,
    ( sk_A
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ ( k2_tarski @ X0 @ X3 ) )
      | ( X2
       != ( k2_tarski @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X3: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X3 ) @ ( k2_tarski @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    r1_tarski @ ( k2_tarski @ sk_B @ sk_C ) @ sk_A ),
    inference('sup+',[status(thm)],['59','61'])).

thf('63',plain,
    ( sk_A
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['57','58'])).

thf('64',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['56','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nwKxpDIWDl
% 0.16/0.37  % Computer   : n015.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 09:31:23 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 63 iterations in 0.023s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(t42_zfmisc_1, conjecture,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.23/0.51       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.23/0.51            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.51        ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.23/0.51          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.23/0.51               ( ( A ) != ( k1_tarski @ C ) ) & 
% 0.23/0.51               ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t42_zfmisc_1])).
% 0.23/0.51  thf('0', plain,
% 0.23/0.51      ((((sk_A) = (k2_tarski @ sk_B @ sk_C))
% 0.23/0.51        | ((sk_A) = (k1_tarski @ sk_C))
% 0.23/0.51        | ((sk_A) = (k1_tarski @ sk_B))
% 0.23/0.51        | ((sk_A) = (k1_xboole_0))
% 0.23/0.51        | (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))
% 0.23/0.51         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('split', [status(esa)], ['0'])).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      ((((sk_A) != (k1_xboole_0))
% 0.23/0.51        | ~ (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      ((~ (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))
% 0.23/0.51         <= (~ ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('split', [status(esa)], ['2'])).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      ((~ (r1_tarski @ sk_A @ sk_A))
% 0.23/0.51         <= (~ ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))) & 
% 0.23/0.51             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '3'])).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      ((((sk_A) != (k1_tarski @ sk_B))
% 0.23/0.51        | ~ (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (~ ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))) | 
% 0.23/0.51       ~ (((sk_A) = (k1_tarski @ sk_B)))),
% 0.23/0.51      inference('split', [status(esa)], ['5'])).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      ((((sk_A) != (k1_tarski @ sk_C))
% 0.23/0.51        | ~ (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      (~ ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))) | 
% 0.23/0.51       ~ (((sk_A) = (k1_tarski @ sk_C)))),
% 0.23/0.51      inference('split', [status(esa)], ['7'])).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      ((((sk_A) != (k2_tarski @ sk_B @ sk_C))
% 0.23/0.51        | ~ (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (~ ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))) | 
% 0.23/0.51       ~ (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.23/0.51      inference('split', [status(esa)], ['9'])).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))
% 0.23/0.51         <= (((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('split', [status(esa)], ['0'])).
% 0.23/0.51  thf(l45_zfmisc_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.23/0.51       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.23/0.51            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.51         (((X2) = (k2_tarski @ X0 @ X1))
% 0.23/0.51          | ((X2) = (k1_tarski @ X1))
% 0.23/0.51          | ((X2) = (k1_tarski @ X0))
% 0.23/0.51          | ((X2) = (k1_xboole_0))
% 0.23/0.51          | ~ (r1_tarski @ X2 @ (k2_tarski @ X0 @ X1)))),
% 0.23/0.51      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      (((((sk_A) = (k1_xboole_0))
% 0.23/0.51         | ((sk_A) = (k1_tarski @ sk_B))
% 0.23/0.51         | ((sk_A) = (k1_tarski @ sk_C))
% 0.23/0.51         | ((sk_A) = (k2_tarski @ sk_B @ sk_C))))
% 0.23/0.51         <= (((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      ((((sk_A) != (k2_tarski @ sk_B @ sk_C)))
% 0.23/0.51         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('split', [status(esa)], ['9'])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (((((sk_A) != (sk_A))
% 0.23/0.51         | ((sk_A) = (k1_tarski @ sk_C))
% 0.23/0.51         | ((sk_A) = (k1_tarski @ sk_B))
% 0.23/0.51         | ((sk_A) = (k1_xboole_0))))
% 0.23/0.51         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.23/0.51             ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      (((((sk_A) = (k1_xboole_0))
% 0.23/0.51         | ((sk_A) = (k1_tarski @ sk_B))
% 0.23/0.51         | ((sk_A) = (k1_tarski @ sk_C))))
% 0.23/0.51         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.23/0.51             ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      ((((sk_A) != (k1_tarski @ sk_C))) <= (~ (((sk_A) = (k1_tarski @ sk_C))))),
% 0.23/0.51      inference('split', [status(esa)], ['7'])).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      (((((sk_A) != (sk_A))
% 0.23/0.51         | ((sk_A) = (k1_tarski @ sk_B))
% 0.23/0.51         | ((sk_A) = (k1_xboole_0))))
% 0.23/0.51         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.23/0.51             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.23/0.51             ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      (((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B))))
% 0.23/0.51         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.23/0.51             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.23/0.51             ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.23/0.51      inference('split', [status(esa)], ['5'])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      (((((sk_A) != (sk_A)) | ((sk_A) = (k1_xboole_0))))
% 0.23/0.51         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.23/0.51             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.23/0.51             ~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.23/0.51             ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      ((((sk_A) = (k1_xboole_0)))
% 0.23/0.51         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.23/0.51             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.23/0.51             ~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.23/0.51             ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.23/0.51      inference('split', [status(esa)], ['2'])).
% 0.23/0.51  thf('24', plain,
% 0.23/0.51      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.23/0.51       ~ ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))),
% 0.23/0.51      inference('split', [status(esa)], ['2'])).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.23/0.51         ((r1_tarski @ X2 @ (k2_tarski @ X0 @ X3)) | ((X2) != (k1_xboole_0)))),
% 0.23/0.51      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.23/0.51  thf('26', plain,
% 0.23/0.51      (![X0 : $i, X3 : $i]: (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X0 @ X3))),
% 0.23/0.51      inference('simplify', [status(thm)], ['25'])).
% 0.23/0.51  thf('27', plain,
% 0.23/0.51      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.51      inference('split', [status(esa)], ['0'])).
% 0.23/0.51  thf('28', plain,
% 0.23/0.51      ((~ (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))
% 0.23/0.51         <= (~ ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('split', [status(esa)], ['2'])).
% 0.23/0.51  thf('29', plain,
% 0.23/0.51      ((~ (r1_tarski @ k1_xboole_0 @ (k2_tarski @ sk_B @ sk_C)))
% 0.23/0.51         <= (~ ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))) & 
% 0.23/0.51             (((sk_A) = (k1_xboole_0))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.23/0.51  thf('30', plain,
% 0.23/0.51      (((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))) | 
% 0.23/0.51       ~ (((sk_A) = (k1_xboole_0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['26', '29'])).
% 0.23/0.51  thf('31', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.23/0.51      inference('sat_resolution*', [status(thm)], ['24', '30'])).
% 0.23/0.51  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.23/0.51      inference('simpl_trail', [status(thm)], ['23', '31'])).
% 0.23/0.51  thf('33', plain,
% 0.23/0.51      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.23/0.51         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.23/0.51             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.23/0.51             ~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.23/0.51             ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['22', '32'])).
% 0.23/0.51  thf('34', plain,
% 0.23/0.51      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.23/0.51       ~ ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))) | 
% 0.23/0.51       (((sk_A) = (k1_tarski @ sk_C))) | (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.23/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.23/0.51  thf('35', plain, (~ ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))),
% 0.23/0.51      inference('sat_resolution*', [status(thm)], ['6', '8', '10', '34'])).
% 0.23/0.51  thf('36', plain,
% 0.23/0.51      ((~ (r1_tarski @ sk_A @ sk_A))
% 0.23/0.51         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('simpl_trail', [status(thm)], ['4', '35'])).
% 0.23/0.51  thf('37', plain,
% 0.23/0.51      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.23/0.51       ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['26', '29'])).
% 0.23/0.51  thf('38', plain,
% 0.23/0.51      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.23/0.51      inference('split', [status(esa)], ['0'])).
% 0.23/0.51  thf('39', plain,
% 0.23/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.23/0.51         ((r1_tarski @ X2 @ (k2_tarski @ X0 @ X3)) | ((X2) != (k1_tarski @ X0)))),
% 0.23/0.51      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.23/0.51  thf('40', plain,
% 0.23/0.51      (![X0 : $i, X3 : $i]:
% 0.23/0.51         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X3))),
% 0.23/0.51      inference('simplify', [status(thm)], ['39'])).
% 0.23/0.51  thf('41', plain,
% 0.23/0.51      ((![X0 : $i]: (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ X0)))
% 0.23/0.51         <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.23/0.51      inference('sup+', [status(thm)], ['38', '40'])).
% 0.23/0.51  thf('42', plain,
% 0.23/0.51      ((((sk_A) != (k2_tarski @ sk_B @ sk_C))
% 0.23/0.51        | ~ (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('43', plain,
% 0.23/0.51      ((~ (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))
% 0.23/0.51         <= (~ ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('split', [status(esa)], ['42'])).
% 0.23/0.51  thf('44', plain, (~ ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))),
% 0.23/0.51      inference('sat_resolution*', [status(thm)], ['6', '8', '10', '34'])).
% 0.23/0.51  thf('45', plain, (~ (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.23/0.51      inference('simpl_trail', [status(thm)], ['43', '44'])).
% 0.23/0.51  thf('46', plain, (~ (((sk_A) = (k1_tarski @ sk_B)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['41', '45'])).
% 0.23/0.51  thf('47', plain,
% 0.23/0.51      (~ ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))) | 
% 0.23/0.51       (((sk_A) = (k1_tarski @ sk_B))) | (((sk_A) = (k1_tarski @ sk_C))) | 
% 0.23/0.51       (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.23/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.23/0.51  thf('48', plain,
% 0.23/0.51      ((((sk_A) = (k1_tarski @ sk_C))) <= ((((sk_A) = (k1_tarski @ sk_C))))),
% 0.23/0.51      inference('split', [status(esa)], ['0'])).
% 0.23/0.51  thf('49', plain,
% 0.23/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.23/0.51         ((r1_tarski @ X2 @ (k2_tarski @ X0 @ X3)) | ((X2) != (k1_tarski @ X3)))),
% 0.23/0.51      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.23/0.51  thf('50', plain,
% 0.23/0.51      (![X0 : $i, X3 : $i]:
% 0.23/0.51         (r1_tarski @ (k1_tarski @ X3) @ (k2_tarski @ X0 @ X3))),
% 0.23/0.51      inference('simplify', [status(thm)], ['49'])).
% 0.23/0.51  thf('51', plain,
% 0.23/0.51      ((![X0 : $i]: (r1_tarski @ sk_A @ (k2_tarski @ X0 @ sk_C)))
% 0.23/0.51         <= ((((sk_A) = (k1_tarski @ sk_C))))),
% 0.23/0.51      inference('sup+', [status(thm)], ['48', '50'])).
% 0.23/0.51  thf('52', plain, (~ (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.23/0.51      inference('simpl_trail', [status(thm)], ['43', '44'])).
% 0.23/0.51  thf('53', plain, (~ (((sk_A) = (k1_tarski @ sk_C)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.23/0.51  thf('54', plain,
% 0.23/0.51      ((((sk_A) = (k2_tarski @ sk_B @ sk_C))) | 
% 0.23/0.51       (((sk_A) = (k1_tarski @ sk_C))) | 
% 0.23/0.51       ((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))) | 
% 0.23/0.51       (((sk_A) = (k1_tarski @ sk_B))) | (((sk_A) = (k1_xboole_0)))),
% 0.23/0.51      inference('split', [status(esa)], ['0'])).
% 0.23/0.51  thf('55', plain, ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.23/0.51      inference('sat_resolution*', [status(thm)],
% 0.23/0.51                ['24', '37', '46', '6', '8', '10', '47', '53', '54'])).
% 0.23/0.51  thf('56', plain, (~ (r1_tarski @ sk_A @ sk_A)),
% 0.23/0.51      inference('simpl_trail', [status(thm)], ['36', '55'])).
% 0.23/0.51  thf('57', plain,
% 0.23/0.51      ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))
% 0.23/0.51         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.23/0.51      inference('split', [status(esa)], ['0'])).
% 0.23/0.51  thf('58', plain, ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.23/0.51      inference('sat_resolution*', [status(thm)],
% 0.23/0.51                ['24', '37', '46', '6', '8', '10', '47', '53', '54'])).
% 0.23/0.51  thf('59', plain, (((sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.23/0.51      inference('simpl_trail', [status(thm)], ['57', '58'])).
% 0.23/0.51  thf('60', plain,
% 0.23/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.23/0.51         ((r1_tarski @ X2 @ (k2_tarski @ X0 @ X3))
% 0.23/0.51          | ((X2) != (k2_tarski @ X0 @ X3)))),
% 0.23/0.51      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.23/0.51  thf('61', plain,
% 0.23/0.51      (![X0 : $i, X3 : $i]:
% 0.23/0.51         (r1_tarski @ (k2_tarski @ X0 @ X3) @ (k2_tarski @ X0 @ X3))),
% 0.23/0.51      inference('simplify', [status(thm)], ['60'])).
% 0.23/0.51  thf('62', plain, ((r1_tarski @ (k2_tarski @ sk_B @ sk_C) @ sk_A)),
% 0.23/0.51      inference('sup+', [status(thm)], ['59', '61'])).
% 0.23/0.51  thf('63', plain, (((sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.23/0.51      inference('simpl_trail', [status(thm)], ['57', '58'])).
% 0.23/0.51  thf('64', plain, ((r1_tarski @ sk_A @ sk_A)),
% 0.23/0.51      inference('demod', [status(thm)], ['62', '63'])).
% 0.23/0.51  thf('65', plain, ($false), inference('demod', [status(thm)], ['56', '64'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.36/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
