%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CrnTm7vUTU

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  99 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  242 ( 589 expanded)
%              Number of equality atoms :   29 (  49 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('0',plain,(
    ! [X38: $i,X41: $i] :
      ( ( X41
        = ( k2_relat_1 @ X38 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X41 @ X38 ) @ ( sk_C_1 @ X41 @ X38 ) ) @ X38 )
      | ( r2_hidden @ ( sk_C_1 @ X41 @ X38 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X28 @ X29 ) @ X30 )
      | ~ ( r2_hidden @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('3',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('6',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('8',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X43 ) @ ( k2_relat_1 @ X43 ) )
      | ~ ( r2_hidden @ X44 @ ( k1_relat_1 @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('13',plain,(
    ! [X33: $i] :
      ( ( v1_relat_1 @ X33 )
      | ( r2_hidden @ ( sk_B @ X33 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('14',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('15',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','15'])).

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

thf('17',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('20',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('24',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['22','23'])).

thf('25',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['18','24'])).

thf('26',plain,(
    r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('28',plain,(
    $false ),
    inference('sup-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CrnTm7vUTU
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:53:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 31 iterations in 0.021s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.21/0.48  thf(d5_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.48       ( ![C:$i]:
% 0.21/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (![X38 : $i, X41 : $i]:
% 0.21/0.48         (((X41) = (k2_relat_1 @ X38))
% 0.21/0.48          | (r2_hidden @ 
% 0.21/0.48             (k4_tarski @ (sk_D_1 @ X41 @ X38) @ (sk_C_1 @ X41 @ X38)) @ X38)
% 0.21/0.48          | (r2_hidden @ (sk_C_1 @ X41 @ X38) @ X41))),
% 0.21/0.48      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.21/0.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.48  thf('1', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.21/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.48  thf(t55_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ (k2_tarski @ X28 @ X29) @ X30)
% 0.21/0.48          | ~ (r2_hidden @ X28 @ X30))),
% 0.21/0.48      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.21/0.48  thf('3', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.48          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.48  thf('5', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('6', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.48          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.48  thf('8', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf(t18_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ~( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X43 : $i, X44 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C_2 @ X43) @ (k2_relat_1 @ X43))
% 0.21/0.48          | ~ (r2_hidden @ X44 @ (k1_relat_1 @ X43))
% 0.21/0.48          | ~ (v1_relat_1 @ X43))),
% 0.21/0.48      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | (r2_hidden @ (sk_C_2 @ X0) @ (k2_relat_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((r2_hidden @ (sk_C_2 @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.48        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.48        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['6', '11'])).
% 0.21/0.48  thf(d1_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) <=>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.48              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X33 : $i]: ((v1_relat_1 @ X33) | (r2_hidden @ (sk_B @ X33) @ X33))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.21/0.48  thf('14', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('15', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (((r2_hidden @ (sk_C_2 @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.48        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '15'])).
% 0.21/0.48  thf(t60_relat_1, conjecture,
% 0.21/0.48    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.48     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.48        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['17'])).
% 0.21/0.48  thf('19', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['17'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain, ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.21/0.48       ~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.48      inference('split', [status(esa)], ['17'])).
% 0.21/0.48  thf('24', plain, (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain, (((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['18', '24'])).
% 0.21/0.48  thf('26', plain, ((r2_hidden @ (sk_C_2 @ k1_xboole_0) @ k1_xboole_0)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['16', '25'])).
% 0.21/0.48  thf('27', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('28', plain, ($false), inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
