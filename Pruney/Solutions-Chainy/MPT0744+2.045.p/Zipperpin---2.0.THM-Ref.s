%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nubX4jp7ok

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:06 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 122 expanded)
%              Number of leaves         :   27 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  548 ( 906 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
            <=> ( r1_ordinal1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('0',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('4',plain,(
    ! [X43: $i] :
      ( ( k1_ordinal1 @ X43 )
      = ( k2_xboole_0 @ X43 @ ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('6',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ ( k3_tarski @ X39 ) )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('10',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( r1_tarski @ sk_A @ ( k3_tarski @ ( k1_tarski @ sk_B_1 ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X40 @ X41 ) )
      = ( k2_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X44 @ X45 )
      | ( r1_tarski @ X44 @ X45 )
      | ~ ( v1_ordinal1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('18',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('20',plain,(
    ! [X42: $i] :
      ( ( v1_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('21',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v3_ordinal1 @ X47 )
      | ~ ( v3_ordinal1 @ X48 )
      | ( r1_ordinal1 @ X47 @ X48 )
      | ~ ( r1_tarski @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('25',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,(
    ! [X43: $i] :
      ( ( k1_ordinal1 @ X43 )
      = ( k2_xboole_0 @ X43 @ ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('33',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('34',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v3_ordinal1 @ X47 )
      | ~ ( v3_ordinal1 @ X48 )
      | ( r1_tarski @ X47 @ X48 )
      | ~ ( r1_ordinal1 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('35',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('39',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_xboole_0 @ X6 @ X8 )
      | ( X6 = X8 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('40',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('41',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v3_ordinal1 @ X50 )
      | ( r2_hidden @ X51 @ X50 )
      | ~ ( r2_xboole_0 @ X51 @ X50 )
      | ~ ( v1_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('42',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X42: $i] :
      ( ( v1_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('45',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['42','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( sk_A = sk_B_1 )
        | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      | ( sk_A = sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['32','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('56',plain,(
    ! [X49: $i] :
      ( r2_hidden @ X49 @ ( k1_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('57',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','30','31','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nubX4jp7ok
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:26:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 231 iterations in 0.109s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.39/0.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.39/0.57  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.39/0.57  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.39/0.57  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.39/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.39/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.57  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.39/0.57  thf(t34_ordinal1, conjecture,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.57           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.39/0.57             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i]:
% 0.39/0.57        ( ( v3_ordinal1 @ A ) =>
% 0.39/0.57          ( ![B:$i]:
% 0.39/0.57            ( ( v3_ordinal1 @ B ) =>
% 0.39/0.57              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.39/0.57                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.39/0.57        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.39/0.57       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (((r1_ordinal1 @ sk_A @ sk_B_1)
% 0.39/0.57        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.57      inference('split', [status(esa)], ['2'])).
% 0.39/0.57  thf(d1_ordinal1, axiom,
% 0.39/0.57    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X43 : $i]:
% 0.39/0.57         ((k1_ordinal1 @ X43) = (k2_xboole_0 @ X43 @ (k1_tarski @ X43)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.39/0.57  thf(d3_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.39/0.57       ( ![D:$i]:
% 0.39/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.57           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X4 @ X2)
% 0.39/0.57          | (r2_hidden @ X4 @ X3)
% 0.39/0.57          | (r2_hidden @ X4 @ X1)
% 0.39/0.57          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.39/0.57         ((r2_hidden @ X4 @ X1)
% 0.39/0.57          | (r2_hidden @ X4 @ X3)
% 0.39/0.57          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.39/0.57          | (r2_hidden @ X1 @ X0)
% 0.39/0.57          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['4', '6'])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))
% 0.39/0.57         | (r2_hidden @ sk_A @ sk_B_1)))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['3', '7'])).
% 0.39/0.57  thf(l49_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X38 : $i, X39 : $i]:
% 0.39/0.57         ((r1_tarski @ X38 @ (k3_tarski @ X39)) | ~ (r2_hidden @ X38 @ X39))),
% 0.39/0.57      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      ((((r2_hidden @ sk_A @ sk_B_1)
% 0.39/0.57         | (r1_tarski @ sk_A @ (k3_tarski @ (k1_tarski @ sk_B_1)))))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf(t69_enumset1, axiom,
% 0.39/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.57  thf(l51_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X40 : $i, X41 : $i]:
% 0.39/0.57         ((k3_tarski @ (k2_tarski @ X40 @ X41)) = (k2_xboole_0 @ X40 @ X41))),
% 0.39/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf(idempotence_k2_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.39/0.57  thf('14', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ X9) = (X9))),
% 0.39/0.57      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.39/0.57  thf('15', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      ((((r2_hidden @ sk_A @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1)))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.57      inference('demod', [status(thm)], ['10', '15'])).
% 0.39/0.57  thf(d2_ordinal1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_ordinal1 @ A ) <=>
% 0.39/0.57       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X44 : $i, X45 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X44 @ X45)
% 0.39/0.57          | (r1_tarski @ X44 @ X45)
% 0.39/0.57          | ~ (v1_ordinal1 @ X45))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      ((((r1_tarski @ sk_A @ sk_B_1)
% 0.39/0.57         | ~ (v1_ordinal1 @ sk_B_1)
% 0.39/0.57         | (r1_tarski @ sk_A @ sk_B_1)))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.57  thf('19', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(cc1_ordinal1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X42 : $i]: ((v1_ordinal1 @ X42) | ~ (v3_ordinal1 @ X42))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.39/0.57  thf('21', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.39/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      ((((r1_tarski @ sk_A @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1)))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.57      inference('demod', [status(thm)], ['18', '21'])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (((r1_tarski @ sk_A @ sk_B_1))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.57      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.57  thf(redefinition_r1_ordinal1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.39/0.57       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X47 : $i, X48 : $i]:
% 0.39/0.57         (~ (v3_ordinal1 @ X47)
% 0.39/0.57          | ~ (v3_ordinal1 @ X48)
% 0.39/0.57          | (r1_ordinal1 @ X47 @ X48)
% 0.39/0.57          | ~ (r1_tarski @ X47 @ X48))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      ((((r1_ordinal1 @ sk_A @ sk_B_1)
% 0.39/0.57         | ~ (v3_ordinal1 @ sk_B_1)
% 0.39/0.57         | ~ (v3_ordinal1 @ sk_A)))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.57  thf('26', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (((r1_ordinal1 @ sk_A @ sk_B_1))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.57      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.39/0.57       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.39/0.57       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.39/0.57      inference('split', [status(esa)], ['2'])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X43 : $i]:
% 0.39/0.57         ((k1_ordinal1 @ X43) = (k2_xboole_0 @ X43 @ (k1_tarski @ X43)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (((r1_ordinal1 @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.57      inference('split', [status(esa)], ['2'])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X47 : $i, X48 : $i]:
% 0.39/0.57         (~ (v3_ordinal1 @ X47)
% 0.39/0.57          | ~ (v3_ordinal1 @ X48)
% 0.39/0.57          | (r1_tarski @ X47 @ X48)
% 0.39/0.57          | ~ (r1_ordinal1 @ X47 @ X48))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      ((((r1_tarski @ sk_A @ sk_B_1)
% 0.39/0.57         | ~ (v3_ordinal1 @ sk_B_1)
% 0.39/0.57         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.57  thf('36', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('37', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      (((r1_tarski @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.39/0.57  thf(d8_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.39/0.57       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (![X6 : $i, X8 : $i]:
% 0.39/0.57         ((r2_xboole_0 @ X6 @ X8) | ((X6) = (X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.39/0.57      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      (((((sk_A) = (sk_B_1)) | (r2_xboole_0 @ sk_A @ sk_B_1)))
% 0.39/0.57         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.57  thf(t21_ordinal1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_ordinal1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.57           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      (![X50 : $i, X51 : $i]:
% 0.39/0.57         (~ (v3_ordinal1 @ X50)
% 0.39/0.57          | (r2_hidden @ X51 @ X50)
% 0.39/0.57          | ~ (r2_xboole_0 @ X51 @ X50)
% 0.39/0.57          | ~ (v1_ordinal1 @ X51))),
% 0.39/0.57      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      (((((sk_A) = (sk_B_1))
% 0.39/0.57         | ~ (v1_ordinal1 @ sk_A)
% 0.39/0.57         | (r2_hidden @ sk_A @ sk_B_1)
% 0.39/0.57         | ~ (v3_ordinal1 @ sk_B_1))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.57  thf('43', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      (![X42 : $i]: ((v1_ordinal1 @ X42) | ~ (v3_ordinal1 @ X42))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.39/0.57  thf('45', plain, ((v1_ordinal1 @ sk_A)),
% 0.39/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.57  thf('46', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('47', plain,
% 0.39/0.57      (((((sk_A) = (sk_B_1)) | (r2_hidden @ sk_A @ sk_B_1)))
% 0.39/0.57         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['42', '45', '46'])).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X0 @ X3)
% 0.39/0.57          | (r2_hidden @ X0 @ X2)
% 0.39/0.57          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.39/0.57  thf('49', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.39/0.57         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.39/0.57      inference('simplify', [status(thm)], ['48'])).
% 0.39/0.57  thf('50', plain,
% 0.39/0.57      ((![X0 : $i]:
% 0.39/0.57          (((sk_A) = (sk_B_1))
% 0.39/0.57           | (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0))))
% 0.39/0.57         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['47', '49'])).
% 0.39/0.57  thf('51', plain,
% 0.39/0.57      ((((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)) | ((sk_A) = (sk_B_1))))
% 0.39/0.57         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['32', '50'])).
% 0.39/0.57  thf('52', plain,
% 0.39/0.57      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.39/0.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('53', plain,
% 0.39/0.57      ((((sk_A) = (sk_B_1)))
% 0.39/0.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.39/0.57             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.39/0.57  thf('54', plain,
% 0.39/0.57      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.39/0.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('55', plain,
% 0.39/0.57      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.39/0.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.39/0.57             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.39/0.57  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.39/0.57  thf('56', plain, (![X49 : $i]: (r2_hidden @ X49 @ (k1_ordinal1 @ X49))),
% 0.39/0.57      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.39/0.57  thf('57', plain,
% 0.39/0.57      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.39/0.57       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['55', '56'])).
% 0.39/0.57  thf('58', plain, ($false),
% 0.39/0.57      inference('sat_resolution*', [status(thm)], ['1', '30', '31', '57'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.42/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
