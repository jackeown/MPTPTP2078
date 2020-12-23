%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cBaV7cl72D

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 228 expanded)
%              Number of leaves         :   20 (  69 expanded)
%              Depth                    :   19
%              Number of atoms          :  614 (1830 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t33_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ B )
            <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_ordinal1])).

thf('0',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('3',plain,(
    ! [X47: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X47 ) )
      | ~ ( v3_ordinal1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('4',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('7',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('13',plain,(
    ! [X41: $i] :
      ( ( k1_ordinal1 @ X41 )
      = ( k2_xboole_0 @ X41 @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v3_ordinal1 @ X45 )
      | ( r2_hidden @ X46 @ X45 )
      | ( X46 = X45 )
      | ( r2_hidden @ X45 @ X46 )
      | ~ ( v3_ordinal1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X48 @ X49 )
      | ~ ( r1_tarski @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('27',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('28',plain,(
    ! [X44: $i] :
      ( r2_hidden @ X44 @ ( k1_ordinal1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('29',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X48 @ X49 )
      | ~ ( r1_tarski @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','31'])).

thf('33',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,(
    ! [X47: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X47 ) )
      | ~ ( v3_ordinal1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('36',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('37',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v3_ordinal1 @ X39 )
      | ~ ( v3_ordinal1 @ X40 )
      | ( r1_ordinal1 @ X39 @ X40 )
      | ( r1_ordinal1 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('47',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X48 @ X49 )
      | ~ ( r1_tarski @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('53',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('57',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
        | ~ ( r1_tarski @ X0 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_A ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','58'])).

thf('60',plain,(
    ! [X41: $i] :
      ( ( k1_ordinal1 @ X41 )
      = ( k2_xboole_0 @ X41 @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('61',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_ordinal1 @ X42 @ X43 )
      | ~ ( r1_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('63',plain,
    ( ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('67',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','31','66'])).

thf('68',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['65','67'])).

thf('69',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','68'])).

thf('70',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['33','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cBaV7cl72D
% 0.12/0.35  % Computer   : n012.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 12:39:22 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 286 iterations in 0.113s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.57  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.20/0.57  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(t33_ordinal1, conjecture,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.57           ( ( r2_hidden @ A @ B ) <=>
% 0.20/0.57             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i]:
% 0.20/0.57        ( ( v3_ordinal1 @ A ) =>
% 0.20/0.57          ( ![B:$i]:
% 0.20/0.57            ( ( v3_ordinal1 @ B ) =>
% 0.20/0.57              ( ( r2_hidden @ A @ B ) <=>
% 0.20/0.57                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.57        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.20/0.57         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.20/0.57       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf(t29_ordinal1, axiom,
% 0.20/0.57    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X47 : $i]:
% 0.20/0.57         ((v3_ordinal1 @ (k1_ordinal1 @ X47)) | ~ (v3_ordinal1 @ X47))),
% 0.20/0.57      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('split', [status(esa)], ['4'])).
% 0.20/0.57  thf(redefinition_r1_ordinal1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.57       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (![X42 : $i, X43 : $i]:
% 0.20/0.57         (~ (v3_ordinal1 @ X42)
% 0.20/0.57          | ~ (v3_ordinal1 @ X43)
% 0.20/0.57          | (r1_tarski @ X42 @ X43)
% 0.20/0.57          | ~ (r1_ordinal1 @ X42 @ X43))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.57         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.57         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.57  thf('8', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.57         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['3', '9'])).
% 0.20/0.57  thf('11', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.57  thf(d1_ordinal1, axiom,
% 0.20/0.57    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X41 : $i]:
% 0.20/0.57         ((k1_ordinal1 @ X41) = (k2_xboole_0 @ X41 @ (k1_tarski @ X41)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.20/0.57  thf(t11_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.20/0.57      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1) | (r1_tarski @ X0 @ X1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      (((r1_tarski @ sk_A @ sk_B))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['12', '15'])).
% 0.20/0.57  thf(t24_ordinal1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.57           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.20/0.57                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (![X45 : $i, X46 : $i]:
% 0.20/0.57         (~ (v3_ordinal1 @ X45)
% 0.20/0.57          | (r2_hidden @ X46 @ X45)
% 0.20/0.57          | ((X46) = (X45))
% 0.20/0.57          | (r2_hidden @ X45 @ X46)
% 0.20/0.57          | ~ (v3_ordinal1 @ X46))),
% 0.20/0.57      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.20/0.57  thf(t7_ordinal1, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      (![X48 : $i, X49 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X48 @ X49) | ~ (r1_tarski @ X49 @ X48))),
% 0.20/0.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (v3_ordinal1 @ X1)
% 0.20/0.57          | (r2_hidden @ X0 @ X1)
% 0.20/0.57          | ((X1) = (X0))
% 0.20/0.57          | ~ (v3_ordinal1 @ X0)
% 0.20/0.57          | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (((~ (v3_ordinal1 @ sk_A)
% 0.20/0.57         | ((sk_B) = (sk_A))
% 0.20/0.57         | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.57         | ~ (v3_ordinal1 @ sk_B)))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['16', '19'])).
% 0.20/0.57  thf('21', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('22', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('23', plain,
% 0.20/0.57      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      ((((sk_B) = (sk_A)))
% 0.20/0.57         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.20/0.57             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 0.20/0.57         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.20/0.57             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.57  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.20/0.57  thf('28', plain, (![X44 : $i]: (r2_hidden @ X44 @ (k1_ordinal1 @ X44))),
% 0.20/0.57      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      (![X48 : $i, X49 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X48 @ X49) | ~ (r1_tarski @ X49 @ X48))),
% 0.20/0.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.57  thf('30', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.20/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.20/0.57       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.57  thf('32', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['2', '31'])).
% 0.20/0.57  thf('33', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      (![X47 : $i]:
% 0.20/0.57         ((v3_ordinal1 @ (k1_ordinal1 @ X47)) | ~ (v3_ordinal1 @ X47))),
% 0.20/0.57      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.20/0.57  thf('35', plain,
% 0.20/0.57      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('split', [status(esa)], ['4'])).
% 0.20/0.57  thf(l1_zfmisc_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.57  thf('36', plain,
% 0.20/0.57      (![X34 : $i, X36 : $i]:
% 0.20/0.57         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 0.20/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.57  thf('37', plain,
% 0.20/0.57      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.20/0.57         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.57  thf('38', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(connectedness_r1_ordinal1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.57       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      (![X39 : $i, X40 : $i]:
% 0.20/0.57         (~ (v3_ordinal1 @ X39)
% 0.20/0.57          | ~ (v3_ordinal1 @ X40)
% 0.20/0.57          | (r1_ordinal1 @ X39 @ X40)
% 0.20/0.57          | (r1_ordinal1 @ X40 @ X39))),
% 0.20/0.57      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((r1_ordinal1 @ X0 @ sk_A)
% 0.20/0.57          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.57          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.57  thf('41', plain,
% 0.20/0.57      (![X42 : $i, X43 : $i]:
% 0.20/0.57         (~ (v3_ordinal1 @ X42)
% 0.20/0.57          | ~ (v3_ordinal1 @ X43)
% 0.20/0.57          | (r1_tarski @ X42 @ X43)
% 0.20/0.57          | ~ (r1_ordinal1 @ X42 @ X43))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.57  thf('42', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v3_ordinal1 @ X0)
% 0.20/0.57          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.57          | (r1_tarski @ X0 @ sk_A)
% 0.20/0.57          | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.57          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.57  thf('43', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('44', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v3_ordinal1 @ X0)
% 0.20/0.57          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.57          | (r1_tarski @ X0 @ sk_A)
% 0.20/0.57          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.57  thf('45', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((r1_tarski @ X0 @ sk_A)
% 0.20/0.57          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.57          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.57  thf('46', plain,
% 0.20/0.57      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('split', [status(esa)], ['4'])).
% 0.20/0.57  thf('47', plain,
% 0.20/0.57      (![X48 : $i, X49 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X48 @ X49) | ~ (r1_tarski @ X49 @ X48))),
% 0.20/0.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.57  thf('48', plain,
% 0.20/0.57      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.57  thf('49', plain,
% 0.20/0.57      (((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_A @ sk_B)))
% 0.20/0.57         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['45', '48'])).
% 0.20/0.57  thf('50', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.57  thf('52', plain,
% 0.20/0.57      (![X42 : $i, X43 : $i]:
% 0.20/0.57         (~ (v3_ordinal1 @ X42)
% 0.20/0.57          | ~ (v3_ordinal1 @ X43)
% 0.20/0.57          | (r1_tarski @ X42 @ X43)
% 0.20/0.57          | ~ (r1_ordinal1 @ X42 @ X43))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.57  thf('53', plain,
% 0.20/0.57      ((((r1_tarski @ sk_A @ sk_B)
% 0.20/0.57         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.57         | ~ (v3_ordinal1 @ sk_A))) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.57  thf('54', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('55', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('56', plain,
% 0.20/0.57      (((r1_tarski @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.20/0.57  thf(t8_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.20/0.57       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.20/0.57  thf('57', plain,
% 0.20/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.57         (~ (r1_tarski @ X3 @ X4)
% 0.20/0.57          | ~ (r1_tarski @ X5 @ X4)
% 0.20/0.57          | (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.20/0.57      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.20/0.57  thf('58', plain,
% 0.20/0.57      ((![X0 : $i]:
% 0.20/0.57          ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.20/0.57           | ~ (r1_tarski @ X0 @ sk_B)))
% 0.20/0.57         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.57  thf('59', plain,
% 0.20/0.57      (((r1_tarski @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_A)) @ sk_B))
% 0.20/0.57         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['37', '58'])).
% 0.20/0.57  thf('60', plain,
% 0.20/0.57      (![X41 : $i]:
% 0.20/0.57         ((k1_ordinal1 @ X41) = (k2_xboole_0 @ X41 @ (k1_tarski @ X41)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.20/0.57  thf('61', plain,
% 0.20/0.57      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.20/0.57         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.57  thf('62', plain,
% 0.20/0.57      (![X42 : $i, X43 : $i]:
% 0.20/0.57         (~ (v3_ordinal1 @ X42)
% 0.20/0.57          | ~ (v3_ordinal1 @ X43)
% 0.20/0.57          | (r1_ordinal1 @ X42 @ X43)
% 0.20/0.57          | ~ (r1_tarski @ X42 @ X43))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.57  thf('63', plain,
% 0.20/0.57      ((((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.57         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.57         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.20/0.57         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.57  thf('64', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('65', plain,
% 0.20/0.57      ((((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.57         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.20/0.57         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.57  thf('66', plain,
% 0.20/0.57      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.20/0.57       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.20/0.57      inference('split', [status(esa)], ['4'])).
% 0.20/0.57  thf('67', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['2', '31', '66'])).
% 0.20/0.57  thf('68', plain,
% 0.20/0.57      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.57        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['65', '67'])).
% 0.20/0.57  thf('69', plain,
% 0.20/0.57      ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['34', '68'])).
% 0.20/0.57  thf('70', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('71', plain, ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.20/0.57      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.57  thf('72', plain, ($false), inference('demod', [status(thm)], ['33', '71'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
