%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T3xFTxOvyl

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:56 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 141 expanded)
%              Number of leaves         :   18 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  549 (1451 expanded)
%              Number of equality atoms :   50 ( 156 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t18_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( ( ( k2_mcart_1 @ A )
              = C )
            | ( ( k2_mcart_1 @ A )
              = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X20 ) @ X22 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k4_xboole_0 @ ( k2_tarski @ sk_C @ sk_D_1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X14 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X13 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X13 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X16 @ X18 ) @ X19 )
        = ( k2_tarski @ X16 @ X18 ) )
      | ( r2_hidden @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_D_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X16 @ X18 ) @ X19 )
        = ( k2_tarski @ X16 @ X18 ) )
      | ( r2_hidden @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X13 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('26',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k4_xboole_0 @ X13 @ ( k1_tarski @ X15 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ sk_A )
        = X0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k4_xboole_0 @ ( k2_tarski @ sk_C @ sk_D_1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ sk_A )
        = X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('34',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_mcart_1 @ X24 )
        = X23 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ ( k1_tarski @ X23 ) @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('35',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( sk_B != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['31'])).

thf('41',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D_1 ),
    inference(simpl_trail,[status(thm)],['32','41'])).

thf('43',plain,(
    r2_hidden @ sk_C @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('45',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ sk_A )
        = X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('47',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['36'])).

thf('49',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('50',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['39','49'])).

thf('51',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['48','50'])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T3xFTxOvyl
% 0.13/0.38  % Computer   : n008.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 11:22:15 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.39  % Python version: Python 3.6.8
% 0.13/0.39  % Running in FO mode
% 0.52/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.76  % Solved by: fo/fo7.sh
% 0.52/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.76  % done 557 iterations in 0.260s
% 0.52/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.76  % SZS output start Refutation
% 0.52/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.76  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.52/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.76  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.52/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.76  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.52/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.76  thf(t18_mcart_1, conjecture,
% 0.52/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.76     ( ( r2_hidden @
% 0.52/0.76         A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.52/0.76       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.52/0.76         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.52/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.76    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.76        ( ( r2_hidden @
% 0.52/0.76            A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.52/0.76          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.52/0.76            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.52/0.76    inference('cnf.neg', [status(esa)], [t18_mcart_1])).
% 0.52/0.76  thf('0', plain,
% 0.52/0.76      ((r2_hidden @ sk_A @ 
% 0.52/0.76        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(t10_mcart_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.52/0.76       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.52/0.76         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.52/0.76  thf('1', plain,
% 0.52/0.76      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.52/0.76         ((r2_hidden @ (k2_mcart_1 @ X20) @ X22)
% 0.52/0.76          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.52/0.76  thf('2', plain,
% 0.52/0.76      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.52/0.76      inference('sup-', [status(thm)], ['0', '1'])).
% 0.52/0.76  thf(d5_xboole_0, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.52/0.76       ( ![D:$i]:
% 0.52/0.76         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.76           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.52/0.76  thf('3', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X0 @ X1)
% 0.52/0.76          | (r2_hidden @ X0 @ X2)
% 0.52/0.76          | (r2_hidden @ X0 @ X3)
% 0.52/0.76          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.52/0.76      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.52/0.76  thf('4', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.52/0.76          | (r2_hidden @ X0 @ X2)
% 0.52/0.76          | ~ (r2_hidden @ X0 @ X1))),
% 0.52/0.76      inference('simplify', [status(thm)], ['3'])).
% 0.52/0.76  thf('5', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((r2_hidden @ (k2_mcart_1 @ sk_A) @ X0)
% 0.52/0.76          | (r2_hidden @ (k2_mcart_1 @ sk_A) @ 
% 0.52/0.76             (k4_xboole_0 @ (k2_tarski @ sk_C @ sk_D_1) @ X0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['2', '4'])).
% 0.52/0.76  thf(t64_zfmisc_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.52/0.76       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.52/0.76  thf('6', plain,
% 0.52/0.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.76         (((X12) != (X14))
% 0.52/0.76          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X13 @ (k1_tarski @ X14))))),
% 0.52/0.76      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.52/0.76  thf('7', plain,
% 0.52/0.76      (![X13 : $i, X14 : $i]:
% 0.52/0.76         ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X13 @ (k1_tarski @ X14)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['6'])).
% 0.52/0.76  thf('8', plain,
% 0.52/0.76      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ (k2_mcart_1 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['5', '7'])).
% 0.52/0.76  thf('9', plain,
% 0.52/0.76      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.52/0.76      inference('sup-', [status(thm)], ['0', '1'])).
% 0.52/0.76  thf(t72_zfmisc_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.52/0.76       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.52/0.76  thf('10', plain,
% 0.52/0.76      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.52/0.76         (((k4_xboole_0 @ (k2_tarski @ X16 @ X18) @ X19)
% 0.52/0.76            = (k2_tarski @ X16 @ X18))
% 0.52/0.76          | (r2_hidden @ X18 @ X19)
% 0.52/0.76          | (r2_hidden @ X16 @ X19))),
% 0.52/0.76      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.52/0.76  thf('11', plain,
% 0.52/0.76      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X4 @ X3)
% 0.52/0.76          | ~ (r2_hidden @ X4 @ X2)
% 0.52/0.76          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.52/0.76      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.52/0.76  thf('12', plain,
% 0.52/0.76      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X4 @ X2)
% 0.52/0.76          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['11'])).
% 0.52/0.76  thf('13', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X3 @ (k2_tarski @ X1 @ X0))
% 0.52/0.76          | (r2_hidden @ X1 @ X2)
% 0.52/0.76          | (r2_hidden @ X0 @ X2)
% 0.52/0.76          | ~ (r2_hidden @ X3 @ X2))),
% 0.52/0.76      inference('sup-', [status(thm)], ['10', '12'])).
% 0.52/0.76  thf('14', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0)
% 0.52/0.76          | (r2_hidden @ sk_D_1 @ X0)
% 0.52/0.76          | (r2_hidden @ sk_C @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['9', '13'])).
% 0.52/0.76  thf('15', plain,
% 0.52/0.76      (((r2_hidden @ sk_C @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 0.52/0.76        | (r2_hidden @ sk_D_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['8', '14'])).
% 0.52/0.76  thf(t69_enumset1, axiom,
% 0.52/0.76    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.52/0.76  thf('16', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.52/0.76      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.76  thf('17', plain,
% 0.52/0.76      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.52/0.76         (((k4_xboole_0 @ (k2_tarski @ X16 @ X18) @ X19)
% 0.52/0.76            = (k2_tarski @ X16 @ X18))
% 0.52/0.76          | (r2_hidden @ X18 @ X19)
% 0.52/0.76          | (r2_hidden @ X16 @ X19))),
% 0.52/0.76      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.52/0.76  thf('18', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k2_tarski @ X0 @ X0))
% 0.52/0.76          | (r2_hidden @ X0 @ X1)
% 0.52/0.76          | (r2_hidden @ X0 @ X1))),
% 0.52/0.76      inference('sup+', [status(thm)], ['16', '17'])).
% 0.52/0.76  thf('19', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((r2_hidden @ X0 @ X1)
% 0.52/0.76          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k2_tarski @ X0 @ X0)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['18'])).
% 0.52/0.76  thf('20', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.52/0.76      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.76  thf('21', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 0.52/0.76          | (r2_hidden @ X1 @ X0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['19', '20'])).
% 0.52/0.76  thf('22', plain,
% 0.52/0.76      (![X13 : $i, X14 : $i]:
% 0.52/0.76         ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X13 @ (k1_tarski @ X14)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['6'])).
% 0.52/0.76  thf('23', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.52/0.76          | (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.76  thf('24', plain,
% 0.52/0.76      (((r2_hidden @ sk_C @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 0.52/0.76        | (r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D_1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['15', '23'])).
% 0.52/0.76  thf('25', plain,
% 0.52/0.76      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.52/0.76      inference('sup-', [status(thm)], ['0', '1'])).
% 0.52/0.76  thf('26', plain,
% 0.52/0.76      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.52/0.76         ((r2_hidden @ X12 @ (k4_xboole_0 @ X13 @ (k1_tarski @ X15)))
% 0.52/0.76          | ((X12) = (X15))
% 0.52/0.76          | ~ (r2_hidden @ X12 @ X13))),
% 0.52/0.76      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.52/0.76  thf('27', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((k2_mcart_1 @ sk_A) = (X0))
% 0.52/0.76          | (r2_hidden @ (k2_mcart_1 @ sk_A) @ 
% 0.52/0.76             (k4_xboole_0 @ (k2_tarski @ sk_C @ sk_D_1) @ (k1_tarski @ X0))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['25', '26'])).
% 0.52/0.76  thf('28', plain,
% 0.52/0.76      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X4 @ X2)
% 0.52/0.76          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['11'])).
% 0.52/0.76  thf('29', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((k2_mcart_1 @ sk_A) = (X0))
% 0.52/0.76          | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ X0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.76  thf('30', plain,
% 0.52/0.76      (((r2_hidden @ sk_C @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 0.52/0.76        | ((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['24', '29'])).
% 0.52/0.76  thf('31', plain,
% 0.52/0.76      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('32', plain,
% 0.52/0.76      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 0.52/0.76         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.52/0.76      inference('split', [status(esa)], ['31'])).
% 0.52/0.76  thf('33', plain,
% 0.52/0.76      ((r2_hidden @ sk_A @ 
% 0.52/0.76        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(t12_mcart_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.52/0.76       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.52/0.76         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.52/0.76  thf('34', plain,
% 0.52/0.76      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.52/0.76         (((k1_mcart_1 @ X24) = (X23))
% 0.52/0.76          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ (k1_tarski @ X23) @ X25)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.52/0.76  thf('35', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.52/0.76      inference('sup-', [status(thm)], ['33', '34'])).
% 0.52/0.76  thf('36', plain,
% 0.52/0.76      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('37', plain,
% 0.52/0.76      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.52/0.76         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.52/0.76      inference('split', [status(esa)], ['36'])).
% 0.52/0.76  thf('38', plain,
% 0.52/0.76      ((((sk_B) != (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['35', '37'])).
% 0.52/0.76  thf('39', plain, ((((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['38'])).
% 0.52/0.76  thf('40', plain,
% 0.52/0.76      (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))) | 
% 0.52/0.76       ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.52/0.76      inference('split', [status(esa)], ['31'])).
% 0.52/0.76  thf('41', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.52/0.76      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.52/0.76  thf('42', plain, (((k2_mcart_1 @ sk_A) != (sk_D_1))),
% 0.52/0.76      inference('simpl_trail', [status(thm)], ['32', '41'])).
% 0.52/0.76  thf('43', plain, ((r2_hidden @ sk_C @ (k1_tarski @ (k2_mcart_1 @ sk_A)))),
% 0.52/0.76      inference('simplify_reflect-', [status(thm)], ['30', '42'])).
% 0.52/0.76  thf('44', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.52/0.76          | (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.76  thf('45', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))),
% 0.52/0.76      inference('sup-', [status(thm)], ['43', '44'])).
% 0.52/0.76  thf('46', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((k2_mcart_1 @ sk_A) = (X0))
% 0.52/0.76          | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ X0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.76  thf('47', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.52/0.76      inference('sup-', [status(thm)], ['45', '46'])).
% 0.52/0.76  thf('48', plain,
% 0.52/0.76      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.52/0.76         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.52/0.76      inference('split', [status(esa)], ['36'])).
% 0.52/0.76  thf('49', plain,
% 0.52/0.76      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.52/0.76      inference('split', [status(esa)], ['36'])).
% 0.52/0.76  thf('50', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.52/0.76      inference('sat_resolution*', [status(thm)], ['39', '49'])).
% 0.52/0.76  thf('51', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.52/0.76      inference('simpl_trail', [status(thm)], ['48', '50'])).
% 0.52/0.76  thf('52', plain, ($false),
% 0.52/0.76      inference('simplify_reflect-', [status(thm)], ['47', '51'])).
% 0.52/0.76  
% 0.52/0.76  % SZS output end Refutation
% 0.52/0.76  
% 0.52/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
