%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0875+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tZWOEojSgs

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:38 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 489 expanded)
%              Number of leaves         :    9 ( 111 expanded)
%              Depth                    :   22
%              Number of atoms          :  739 (5786 expanded)
%              Number of equality atoms :  175 (1451 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t35_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) )
      <=> ( ( k3_zfmisc_1 @ A @ B @ C )
         != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t35_mcart_1])).

thf('0',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k3_zfmisc_1 @ sk_A @ X1 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','8'])).

thf('10',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k3_zfmisc_1 @ sk_A @ X1 @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( $false
   <= ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('19',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('30',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('33',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( sk_C != k1_xboole_0 )
      & ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_C != k1_xboole_0 )
      & ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('36',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('39',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['18','20','22','40'])).

thf('42',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['17','41'])).

thf('43',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('44',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('45',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('46',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('48',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_C )
        = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','50'])).

thf('52',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_C )
        = sk_C )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('55',plain,(
    ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['18','20','22','40'])).

thf('56',plain,(
    ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    sk_C != k1_xboole_0 ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,(
    sk_B = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['42','18','43','44','45','60','61'])).

thf('63',plain,(
    sk_B = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','62'])).

thf('64',plain,(
    ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['54','55'])).

thf('65',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k3_zfmisc_1 @ X1 @ sk_B @ X0 )
        = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k3_zfmisc_1 @ X1 @ sk_B @ X0 )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    sk_B = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['42','18','43','44','45','60','61'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ sk_B @ X0 )
      = sk_B ) ),
    inference(simpl_trail,[status(thm)],['73','74'])).

thf('76',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['64','75'])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['63','76'])).


%------------------------------------------------------------------------------
