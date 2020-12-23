%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0247+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eKnErZzFx4

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
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
