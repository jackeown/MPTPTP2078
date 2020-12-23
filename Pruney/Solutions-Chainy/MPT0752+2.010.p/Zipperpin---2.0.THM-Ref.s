%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VwCPeDYiSE

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  72 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  225 ( 360 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t45_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v5_ordinal1 @ k1_xboole_0 )
        & ( v1_funct_1 @ k1_xboole_0 )
        & ( v5_relat_1 @ k1_xboole_0 @ A )
        & ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t45_ordinal1])).

thf('0',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
   <= ~ ( v5_ordinal1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('3',plain,
    ( ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A )
   <= ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v5_relat_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('5',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
   <= ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( v5_ordinal1 @ k1_xboole_0 ) ),
    inference('sat_resolution*',[status(thm)],['4','9','14','15'])).

thf('17',plain,(
    ~ ( v5_ordinal1 @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf(rc3_ordinal1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v5_ordinal1 @ B )
      & ( v1_funct_1 @ B )
      & ( v5_relat_1 @ B @ A )
      & ( v1_relat_1 @ B ) ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( v5_relat_1 @ ( sk_B @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v5_relat_1 @ X1 @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( sk_B @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('24',plain,
    ( ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X5: $i] :
      ( ( ( k2_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    | ( ( sk_B @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( sk_B @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( sk_B @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X9: $i] :
      ( v5_ordinal1 @ ( sk_B @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('31',plain,(
    v5_ordinal1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['17','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VwCPeDYiSE
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 35 iterations in 0.014s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.48  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(t45_ordinal1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.21/0.48       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.21/0.48          ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t45_ordinal1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((~ (v5_ordinal1 @ k1_xboole_0)
% 0.21/0.48        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.48        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.48        | ~ (v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((~ (v5_ordinal1 @ k1_xboole_0)) <= (~ ((v5_ordinal1 @ k1_xboole_0)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf(l222_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.21/0.48  thf('2', plain, (![X3 : $i]: (v5_relat_1 @ k1_xboole_0 @ X3)),
% 0.21/0.48      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((~ (v5_relat_1 @ k1_xboole_0 @ sk_A))
% 0.21/0.48         <= (~ ((v5_relat_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('4', plain, (((v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.48  thf('5', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.48  thf(fc3_funct_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.48       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.48  thf('6', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.48  thf('7', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ k1_xboole_0)) <= (~ ((v1_relat_1 @ k1_xboole_0)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('9', plain, (((v1_relat_1 @ k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf(cc1_funct_1, axiom,
% 0.21/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.21/0.48  thf('10', plain, (![X6 : $i]: ((v1_funct_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((~ (v1_funct_1 @ k1_xboole_0)) <= (~ ((v1_funct_1 @ k1_xboole_0)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((~ (v1_xboole_0 @ k1_xboole_0)) <= (~ ((v1_funct_1 @ k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.48  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.48  thf('14', plain, (((v1_funct_1 @ k1_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (~ ((v5_ordinal1 @ k1_xboole_0)) | ~ ((v1_funct_1 @ k1_xboole_0)) | 
% 0.21/0.48       ~ ((v1_relat_1 @ k1_xboole_0)) | ~ ((v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('16', plain, (~ ((v5_ordinal1 @ k1_xboole_0))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['4', '9', '14', '15'])).
% 0.21/0.48  thf('17', plain, (~ (v5_ordinal1 @ k1_xboole_0)),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.21/0.48  thf(rc3_ordinal1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ?[B:$i]:
% 0.21/0.48       ( ( v5_ordinal1 @ B ) & ( v1_funct_1 @ B ) & ( v5_relat_1 @ B @ A ) & 
% 0.21/0.48         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.48  thf('18', plain, (![X9 : $i]: (v5_relat_1 @ (sk_B @ X9) @ X9)),
% 0.21/0.48      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.21/0.48  thf(d19_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (v5_relat_1 @ X1 @ X2)
% 0.21/0.48          | (r1_tarski @ (k2_relat_1 @ X1) @ X2)
% 0.21/0.48          | ~ (v1_relat_1 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ (sk_B @ X0))
% 0.21/0.48          | (r1_tarski @ (k2_relat_1 @ (sk_B @ X0)) @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain, (![X9 : $i]: (v1_relat_1 @ (sk_B @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.21/0.48  thf('22', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (sk_B @ X0)) @ X0)),
% 0.21/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf(t3_xboole_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.48  thf('24', plain, (((k2_relat_1 @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf(t64_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.48         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X5 : $i]:
% 0.21/0.48         (((k2_relat_1 @ X5) != (k1_xboole_0))
% 0.21/0.48          | ((X5) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0))
% 0.21/0.48        | ((sk_B @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.48  thf('27', plain, (![X9 : $i]: (v1_relat_1 @ (sk_B @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48        | ((sk_B @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('29', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.48  thf('30', plain, (![X9 : $i]: (v5_ordinal1 @ (sk_B @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.21/0.48  thf('31', plain, ((v5_ordinal1 @ k1_xboole_0)),
% 0.21/0.48      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain, ($false), inference('demod', [status(thm)], ['17', '31'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.34/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
