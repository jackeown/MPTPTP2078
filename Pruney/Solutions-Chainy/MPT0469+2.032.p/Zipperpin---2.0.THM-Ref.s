%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qonTARv1iA

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 (  95 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  387 ( 625 expanded)
%              Number of equality atoms :   65 ( 107 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('0',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15
        = ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X15 @ X12 ) @ ( sk_D @ X15 @ X12 ) ) @ X12 )
      | ( r2_hidden @ ( sk_C @ X15 @ X12 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('9',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t26_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X21 @ X20 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X21 ) @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('20',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf('28',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','21'])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','30'])).

thf('32',plain,
    ( $false
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('34',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['32','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qonTARv1iA
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 43 iterations in 0.024s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.48  thf(t60_relat_1, conjecture,
% 0.20/0.48    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.48     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.48        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.48         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf(d4_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X12 : $i, X15 : $i]:
% 0.20/0.48         (((X15) = (k1_relat_1 @ X12))
% 0.20/0.48          | (r2_hidden @ 
% 0.20/0.48             (k4_tarski @ (sk_C @ X15 @ X12) @ (sk_D @ X15 @ X12)) @ X12)
% 0.20/0.48          | (r2_hidden @ (sk_C @ X15 @ X12) @ X15))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.48  thf(t113_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.48  thf(t152_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]: ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.20/0.48  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.20/0.48          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '6'])).
% 0.20/0.48  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('9', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf(dt_k4_relat_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X17 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X17)) | ~ (v1_relat_1 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.48  thf(t37_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.20/0.48         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X22 : $i]:
% 0.20/0.48         (((k1_relat_1 @ X22) = (k2_relat_1 @ (k4_relat_1 @ X22)))
% 0.20/0.48          | ~ (v1_relat_1 @ X22))),
% 0.20/0.48      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.48  thf(t1_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.48  thf('12', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.48  thf(t26_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( v1_relat_1 @ B ) =>
% 0.20/0.48           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 0.20/0.48             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X20 : $i, X21 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X20)
% 0.20/0.48          | ((k2_relat_1 @ (k2_xboole_0 @ X21 @ X20))
% 0.20/0.48              = (k2_xboole_0 @ (k2_relat_1 @ X21) @ (k2_relat_1 @ X20)))
% 0.20/0.48          | ~ (v1_relat_1 @ X21))),
% 0.20/0.48      inference('cnf', [status(esa)], [t26_relat_1])).
% 0.20/0.48  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.48  thf(t15_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.48       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         (((X2) = (k1_xboole_0)) | ((k2_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k2_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.20/0.48          | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.48  thf(fc6_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.48  thf('22', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.20/0.48          | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['18', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.20/0.48          | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0)
% 0.20/0.48          | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ((k1_relat_1 @ X0) != (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.20/0.48          | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.48        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '26'])).
% 0.20/0.48  thf('28', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.48         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.48      inference('demod', [status(thm)], ['1', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (($false) <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.48  thf('33', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.48         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.48         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('36', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.20/0.48       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('38', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain, ($false),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['32', '38'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
