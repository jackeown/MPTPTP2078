%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lzgIxbGwrJ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:10 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 310 expanded)
%              Number of leaves         :   20 (  83 expanded)
%              Depth                    :   20
%              Number of atoms          :  536 (2325 expanded)
%              Number of equality atoms :   53 ( 328 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t39_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
      <=> ( ( A = k1_xboole_0 )
          | ( A
            = ( k1_tarski @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_zfmisc_1])).

thf('0',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('6',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('10',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['6','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['5','12'])).

thf('14',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('16',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['3','16','18'])).

thf('20',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['19'])).

thf('21',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf('22',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('27',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['19','26'])).

thf('28',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['25','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','28'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('31',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
      | ( r2_hidden @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('32',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B_1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','39'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('41',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('42',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['5','12'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
      | ( r2_hidden @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('48',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','56'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('58',plain,(
    ! [X44: $i,X46: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X44 ) @ X46 )
      | ~ ( r2_hidden @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('61',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('65',plain,
    ( ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
      = sk_A )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('67',plain,
    ( ( k1_xboole_0 = sk_A )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['5','12'])).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','69'])).

thf('71',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['40','70'])).

thf('72',plain,(
    ! [X44: $i,X46: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X44 ) @ X46 )
      | ~ ( r2_hidden @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('73',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['29','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lzgIxbGwrJ
% 0.17/0.37  % Computer   : n010.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 17:06:14 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.41/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.58  % Solved by: fo/fo7.sh
% 0.41/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.58  % done 176 iterations in 0.099s
% 0.41/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.58  % SZS output start Refutation
% 0.41/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.58  thf(t39_zfmisc_1, conjecture,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.41/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.41/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.58    (~( ![A:$i,B:$i]:
% 0.41/0.58        ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.41/0.58          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ) )),
% 0.41/0.58    inference('cnf.neg', [status(esa)], [t39_zfmisc_1])).
% 0.41/0.58  thf('0', plain,
% 0.41/0.58      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.41/0.58        | ((sk_A) = (k1_xboole_0))
% 0.41/0.58        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('1', plain,
% 0.41/0.58      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.41/0.58         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.41/0.58      inference('split', [status(esa)], ['0'])).
% 0.41/0.58  thf('2', plain,
% 0.41/0.58      ((((sk_A) != (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('3', plain,
% 0.41/0.58      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.41/0.58         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.41/0.58      inference('split', [status(esa)], ['2'])).
% 0.41/0.58  thf('4', plain,
% 0.41/0.58      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.41/0.58        | ((sk_A) = (k1_xboole_0))
% 0.41/0.58        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('5', plain,
% 0.41/0.58      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.41/0.58      inference('split', [status(esa)], ['2'])).
% 0.41/0.58  thf('6', plain,
% 0.41/0.58      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.41/0.58       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.41/0.58      inference('split', [status(esa)], ['2'])).
% 0.41/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.58  thf('7', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.41/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.58  thf('8', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.58      inference('split', [status(esa)], ['0'])).
% 0.41/0.58  thf('9', plain,
% 0.41/0.58      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.41/0.58         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.41/0.58      inference('split', [status(esa)], ['2'])).
% 0.41/0.58  thf('10', plain,
% 0.41/0.58      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_B_1)))
% 0.41/0.58         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))) & 
% 0.41/0.58             (((sk_A) = (k1_xboole_0))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.58  thf('11', plain,
% 0.41/0.59      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))) | 
% 0.41/0.59       ~ (((sk_A) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['7', '10'])).
% 0.41/0.59  thf('12', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['6', '11'])).
% 0.41/0.59  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['5', '12'])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.41/0.59        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.41/0.59      inference('simplify_reflect-', [status(thm)], ['4', '13'])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.41/0.59         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.41/0.59      inference('split', [status(esa)], ['2'])).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      ((((sk_A) = (k1_tarski @ sk_B_1)))
% 0.41/0.59         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.41/0.59  thf(d10_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.59  thf('18', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.41/0.59      inference('simplify', [status(thm)], ['17'])).
% 0.41/0.59  thf('19', plain, (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.41/0.59      inference('demod', [status(thm)], ['3', '16', '18'])).
% 0.41/0.59  thf('20', plain, (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['19'])).
% 0.41/0.59  thf('21', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (![X10 : $i, X12 : $i]:
% 0.41/0.59         (((X10) = (X12))
% 0.41/0.59          | ~ (r1_tarski @ X12 @ X10)
% 0.41/0.59          | ~ (r1_tarski @ X10 @ X12))),
% 0.41/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      ((~ (r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.41/0.59        | ((k1_tarski @ sk_B_1) = (sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      ((((sk_A) != (k1_tarski @ sk_B_1))
% 0.41/0.59        | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      ((((sk_A) != (k1_tarski @ sk_B_1)))
% 0.41/0.59         <= (~ (((sk_A) = (k1_tarski @ sk_B_1))))),
% 0.41/0.59      inference('split', [status(esa)], ['24'])).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      (~ (((sk_A) = (k1_tarski @ sk_B_1))) | 
% 0.41/0.59       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.41/0.59      inference('split', [status(esa)], ['24'])).
% 0.41/0.59  thf('27', plain, (~ (((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['19', '26'])).
% 0.41/0.59  thf('28', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['25', '27'])).
% 0.41/0.59  thf('29', plain, (~ (r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.41/0.59      inference('simplify_reflect-', [status(thm)], ['23', '28'])).
% 0.41/0.59  thf(d1_xboole_0, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.59  thf(l27_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.41/0.59  thf('31', plain,
% 0.41/0.59      (![X47 : $i, X48 : $i]:
% 0.41/0.59         ((r1_xboole_0 @ (k1_tarski @ X47) @ X48) | (r2_hidden @ X47 @ X48))),
% 0.41/0.59      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.41/0.59  thf('32', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.41/0.59  thf(t28_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.59  thf('33', plain,
% 0.41/0.59      (![X13 : $i, X14 : $i]:
% 0.41/0.59         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.59  thf('34', plain, (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.59  thf(t4_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.41/0.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.41/0.59          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.41/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.41/0.59  thf('37', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.41/0.59          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.59  thf('38', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.59          | ~ (r1_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['34', '37'])).
% 0.41/0.59  thf('39', plain,
% 0.41/0.59      (![X0 : $i]: ((r2_hidden @ sk_B_1 @ sk_A) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['31', '38'])).
% 0.41/0.59  thf('40', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B_1 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['30', '39'])).
% 0.41/0.59  thf(l13_xboole_0, axiom,
% 0.41/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.59  thf('41', plain,
% 0.41/0.59      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 0.41/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 0.41/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.41/0.59  thf('43', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.59      inference('sup+', [status(thm)], ['41', '42'])).
% 0.41/0.59  thf('44', plain, (((sk_A) != (k1_xboole_0))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['5', '12'])).
% 0.41/0.59  thf('45', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (((X0) != (k1_xboole_0))
% 0.41/0.59          | ~ (v1_xboole_0 @ X0)
% 0.41/0.59          | ~ (v1_xboole_0 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.41/0.59  thf('46', plain, ((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['45'])).
% 0.41/0.59  thf('47', plain,
% 0.41/0.59      (![X47 : $i, X48 : $i]:
% 0.41/0.59         ((r1_xboole_0 @ (k1_tarski @ X47) @ X48) | (r2_hidden @ X47 @ X48))),
% 0.41/0.59      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.41/0.59  thf('48', plain,
% 0.41/0.59      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.59  thf('49', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.41/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.59  thf('50', plain,
% 0.41/0.59      (![X13 : $i, X14 : $i]:
% 0.41/0.59         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.59  thf('51', plain,
% 0.41/0.59      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['49', '50'])).
% 0.41/0.59  thf('52', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.59  thf('53', plain,
% 0.41/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['51', '52'])).
% 0.41/0.59  thf('54', plain,
% 0.41/0.59      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.41/0.59          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.41/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.41/0.59  thf('55', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.59  thf('56', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['48', '55'])).
% 0.41/0.59  thf('57', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((r2_hidden @ X0 @ k1_xboole_0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['47', '56'])).
% 0.41/0.59  thf(l1_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.41/0.59  thf('58', plain,
% 0.41/0.59      (![X44 : $i, X46 : $i]:
% 0.41/0.59         ((r1_tarski @ (k1_tarski @ X44) @ X46) | ~ (r2_hidden @ X44 @ X46))),
% 0.41/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.41/0.59  thf('59', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ k1_xboole_0)
% 0.41/0.59          | (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['57', '58'])).
% 0.41/0.59  thf('60', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.41/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.59  thf('61', plain,
% 0.41/0.59      (![X10 : $i, X12 : $i]:
% 0.41/0.59         (((X10) = (X12))
% 0.41/0.59          | ~ (r1_tarski @ X12 @ X10)
% 0.41/0.59          | ~ (r1_tarski @ X10 @ X12))),
% 0.41/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.59  thf('62', plain,
% 0.41/0.59      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['60', '61'])).
% 0.41/0.59  thf('63', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ k1_xboole_0) | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['59', '62'])).
% 0.41/0.59  thf('64', plain, (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.59  thf('65', plain,
% 0.41/0.59      ((((k3_xboole_0 @ sk_A @ k1_xboole_0) = (sk_A))
% 0.41/0.59        | (v1_xboole_0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['63', '64'])).
% 0.41/0.59  thf('66', plain,
% 0.41/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['51', '52'])).
% 0.41/0.59  thf('67', plain, ((((k1_xboole_0) = (sk_A)) | (v1_xboole_0 @ k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['65', '66'])).
% 0.41/0.59  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['5', '12'])).
% 0.41/0.59  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.59      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 0.41/0.59  thf('70', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.41/0.59      inference('demod', [status(thm)], ['46', '69'])).
% 0.41/0.59  thf('71', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.41/0.59      inference('clc', [status(thm)], ['40', '70'])).
% 0.41/0.59  thf('72', plain,
% 0.41/0.59      (![X44 : $i, X46 : $i]:
% 0.41/0.59         ((r1_tarski @ (k1_tarski @ X44) @ X46) | ~ (r2_hidden @ X44 @ X46))),
% 0.41/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.41/0.59  thf('73', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.41/0.59      inference('sup-', [status(thm)], ['71', '72'])).
% 0.41/0.59  thf('74', plain, ($false), inference('demod', [status(thm)], ['29', '73'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
