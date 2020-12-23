%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Btqgr45zTn

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:19 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 146 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  440 (1683 expanded)
%              Number of equality atoms :   89 ( 391 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17
        = ( k1_tarski @ X16 ) )
      | ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('14',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17
        = ( k1_tarski @ X16 ) )
      | ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('20',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('26',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['13','15','27'])).

thf('29',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['12','28'])).

thf('30',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('33',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X3 @ X4 ) @ ( k4_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('39',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','41'])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','42'])).

thf('44',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['12','28'])).

thf('45',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('47',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','47'])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','29','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Btqgr45zTn
% 0.12/0.32  % Computer   : n004.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 13:03:09 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.32  % Python version: Python 3.6.8
% 0.12/0.32  % Running in FO mode
% 0.18/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.48  % Solved by: fo/fo7.sh
% 0.18/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.48  % done 96 iterations in 0.055s
% 0.18/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.48  % SZS output start Refutation
% 0.18/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.18/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.18/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.18/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.18/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.18/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.48  thf(t43_zfmisc_1, conjecture,
% 0.18/0.48    (![A:$i,B:$i,C:$i]:
% 0.18/0.48     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.18/0.48          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.18/0.48          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.18/0.48          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.18/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.18/0.48        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.18/0.48             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.18/0.48             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.18/0.48             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.18/0.48    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.18/0.48  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.48  thf(commutativity_k2_tarski, axiom,
% 0.18/0.48    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.18/0.48  thf('1', plain,
% 0.18/0.48      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.18/0.48      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.18/0.48  thf(l51_zfmisc_1, axiom,
% 0.18/0.48    (![A:$i,B:$i]:
% 0.18/0.48     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.18/0.48  thf('2', plain,
% 0.18/0.48      (![X19 : $i, X20 : $i]:
% 0.18/0.48         ((k3_tarski @ (k2_tarski @ X19 @ X20)) = (k2_xboole_0 @ X19 @ X20))),
% 0.18/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.18/0.48  thf('3', plain,
% 0.18/0.48      (![X0 : $i, X1 : $i]:
% 0.18/0.48         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.18/0.48      inference('sup+', [status(thm)], ['1', '2'])).
% 0.18/0.48  thf('4', plain,
% 0.18/0.48      (![X19 : $i, X20 : $i]:
% 0.18/0.48         ((k3_tarski @ (k2_tarski @ X19 @ X20)) = (k2_xboole_0 @ X19 @ X20))),
% 0.18/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.18/0.48  thf('5', plain,
% 0.18/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.18/0.48      inference('sup+', [status(thm)], ['3', '4'])).
% 0.18/0.48  thf(t7_xboole_1, axiom,
% 0.18/0.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.18/0.48  thf('6', plain,
% 0.18/0.48      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.18/0.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.18/0.48  thf('7', plain,
% 0.18/0.48      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.18/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.18/0.48  thf('8', plain, ((r1_tarski @ sk_C @ (k1_tarski @ sk_A))),
% 0.18/0.48      inference('sup+', [status(thm)], ['0', '7'])).
% 0.18/0.48  thf(l3_zfmisc_1, axiom,
% 0.18/0.48    (![A:$i,B:$i]:
% 0.18/0.48     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.18/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.18/0.48  thf('9', plain,
% 0.18/0.48      (![X16 : $i, X17 : $i]:
% 0.18/0.48         (((X17) = (k1_tarski @ X16))
% 0.18/0.48          | ((X17) = (k1_xboole_0))
% 0.18/0.48          | ~ (r1_tarski @ X17 @ (k1_tarski @ X16)))),
% 0.18/0.48      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.18/0.48  thf('10', plain,
% 0.18/0.48      ((((sk_C) = (k1_xboole_0)) | ((sk_C) = (k1_tarski @ sk_A)))),
% 0.18/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.18/0.48  thf('11', plain,
% 0.18/0.48      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.48  thf('12', plain,
% 0.18/0.48      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.18/0.48      inference('split', [status(esa)], ['11'])).
% 0.18/0.48  thf('13', plain,
% 0.18/0.48      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.18/0.48      inference('split', [status(esa)], ['11'])).
% 0.18/0.48  thf('14', plain,
% 0.18/0.48      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.48  thf('15', plain,
% 0.18/0.48      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.18/0.48      inference('split', [status(esa)], ['14'])).
% 0.18/0.48  thf('16', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.48  thf('17', plain,
% 0.18/0.48      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.18/0.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.18/0.48  thf('18', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.18/0.48      inference('sup+', [status(thm)], ['16', '17'])).
% 0.18/0.48  thf('19', plain,
% 0.18/0.48      (![X16 : $i, X17 : $i]:
% 0.18/0.48         (((X17) = (k1_tarski @ X16))
% 0.18/0.48          | ((X17) = (k1_xboole_0))
% 0.18/0.48          | ~ (r1_tarski @ X17 @ (k1_tarski @ X16)))),
% 0.18/0.48      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.18/0.48  thf('20', plain,
% 0.18/0.48      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.18/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.18/0.48  thf('21', plain,
% 0.18/0.48      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.48  thf('22', plain,
% 0.18/0.48      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.18/0.48      inference('split', [status(esa)], ['21'])).
% 0.18/0.48  thf('23', plain,
% 0.18/0.48      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.18/0.48         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.18/0.48      inference('sup-', [status(thm)], ['20', '22'])).
% 0.18/0.48  thf('24', plain,
% 0.18/0.48      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.18/0.48      inference('simplify', [status(thm)], ['23'])).
% 0.18/0.48  thf('25', plain,
% 0.18/0.48      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.18/0.48      inference('split', [status(esa)], ['11'])).
% 0.18/0.48  thf('26', plain,
% 0.18/0.48      ((((sk_B) != (sk_B)))
% 0.18/0.48         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.18/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.18/0.48  thf('27', plain,
% 0.18/0.48      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.18/0.48      inference('simplify', [status(thm)], ['26'])).
% 0.18/0.48  thf('28', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.18/0.48      inference('sat_resolution*', [status(thm)], ['13', '15', '27'])).
% 0.18/0.48  thf('29', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.18/0.48      inference('simpl_trail', [status(thm)], ['12', '28'])).
% 0.18/0.48  thf('30', plain,
% 0.18/0.48      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.18/0.48      inference('split', [status(esa)], ['21'])).
% 0.18/0.48  thf('31', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.48  thf('32', plain,
% 0.18/0.48      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.18/0.48      inference('simplify', [status(thm)], ['23'])).
% 0.18/0.48  thf(t2_boole, axiom,
% 0.18/0.48    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.18/0.48  thf('33', plain,
% 0.18/0.48      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.18/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.18/0.48  thf(t51_xboole_1, axiom,
% 0.18/0.48    (![A:$i,B:$i]:
% 0.18/0.48     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.18/0.48       ( A ) ))).
% 0.18/0.48  thf('34', plain,
% 0.18/0.48      (![X3 : $i, X4 : $i]:
% 0.18/0.48         ((k2_xboole_0 @ (k3_xboole_0 @ X3 @ X4) @ (k4_xboole_0 @ X3 @ X4))
% 0.18/0.48           = (X3))),
% 0.18/0.48      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.18/0.48  thf('35', plain,
% 0.18/0.48      (![X0 : $i]:
% 0.18/0.48         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.18/0.48      inference('sup+', [status(thm)], ['33', '34'])).
% 0.18/0.48  thf('36', plain,
% 0.18/0.48      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.18/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.18/0.48  thf(t100_xboole_1, axiom,
% 0.18/0.48    (![A:$i,B:$i]:
% 0.18/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.18/0.48  thf('37', plain,
% 0.18/0.48      (![X0 : $i, X1 : $i]:
% 0.18/0.48         ((k4_xboole_0 @ X0 @ X1)
% 0.18/0.48           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.18/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.18/0.48  thf('38', plain,
% 0.18/0.48      (![X0 : $i]:
% 0.18/0.48         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.18/0.48      inference('sup+', [status(thm)], ['36', '37'])).
% 0.18/0.48  thf(t5_boole, axiom,
% 0.18/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.18/0.48  thf('39', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.18/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.18/0.48  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.18/0.48      inference('sup+', [status(thm)], ['38', '39'])).
% 0.18/0.48  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.18/0.48      inference('demod', [status(thm)], ['35', '40'])).
% 0.18/0.48  thf('42', plain,
% 0.18/0.48      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.18/0.48         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.18/0.48      inference('sup+', [status(thm)], ['32', '41'])).
% 0.18/0.48  thf('43', plain,
% 0.18/0.48      ((((k1_tarski @ sk_A) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.18/0.48      inference('sup+', [status(thm)], ['31', '42'])).
% 0.18/0.48  thf('44', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.18/0.48      inference('simpl_trail', [status(thm)], ['12', '28'])).
% 0.18/0.48  thf('45', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.18/0.48      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.18/0.48  thf('46', plain,
% 0.18/0.48      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.18/0.48      inference('split', [status(esa)], ['21'])).
% 0.18/0.48  thf('47', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.18/0.48      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 0.18/0.48  thf('48', plain, (((sk_C) != (k1_xboole_0))),
% 0.18/0.48      inference('simpl_trail', [status(thm)], ['30', '47'])).
% 0.18/0.48  thf('49', plain, ($false),
% 0.18/0.48      inference('simplify_reflect-', [status(thm)], ['10', '29', '48'])).
% 0.18/0.48  
% 0.18/0.48  % SZS output end Refutation
% 0.18/0.48  
% 0.18/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
