%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bREp1gdEAF

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 105 expanded)
%              Number of leaves         :   19 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  270 ( 700 expanded)
%              Number of equality atoms :   38 (  86 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('0',plain,(
    ! [X35: $i,X38: $i] :
      ( ( X38
        = ( k2_relat_1 @ X35 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X38 @ X35 ) @ ( sk_C @ X38 @ X35 ) ) @ X35 )
      | ( r2_hidden @ ( sk_C @ X38 @ X35 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 != X29 )
      | ~ ( r2_hidden @ X27 @ ( k4_xboole_0 @ X28 @ ( k1_tarski @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('3',plain,(
    ! [X28: $i,X29: $i] :
      ~ ( r2_hidden @ X29 @ ( k4_xboole_0 @ X28 @ ( k1_tarski @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('7',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('9',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) )).

thf('11',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X42 ) @ ( k2_relat_1 @ X42 ) )
      | ~ ( r2_hidden @ X43 @ ( k1_relat_1 @ X42 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_zfmisc_1 @ X25 @ X26 )
        = k1_xboole_0 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X26: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X26 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X40: $i,X41: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','17'])).

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

thf('19',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('22',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('23',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('26',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['24','25'])).

thf('27',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['20','26'])).

thf('28',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('30',plain,(
    $false ),
    inference('sup-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bREp1gdEAF
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 64 iterations in 0.021s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(d5_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.48       ( ![C:$i]:
% 0.21/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (![X35 : $i, X38 : $i]:
% 0.21/0.48         (((X38) = (k2_relat_1 @ X35))
% 0.21/0.48          | (r2_hidden @ 
% 0.21/0.48             (k4_tarski @ (sk_D @ X38 @ X35) @ (sk_C @ X38 @ X35)) @ X35)
% 0.21/0.48          | (r2_hidden @ (sk_C @ X38 @ X35) @ X38))),
% 0.21/0.48      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.21/0.48  thf(t4_boole, axiom,
% 0.21/0.48    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.48  thf(t64_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.48       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.48         (((X27) != (X29))
% 0.21/0.48          | ~ (r2_hidden @ X27 @ (k4_xboole_0 @ X28 @ (k1_tarski @ X29))))),
% 0.21/0.48      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X28 : $i, X29 : $i]:
% 0.21/0.48         ~ (r2_hidden @ X29 @ (k4_xboole_0 @ X28 @ (k1_tarski @ X29)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.48  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.48          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.48  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.48  thf('7', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.48          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.48  thf('9', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf(t18_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ~( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X42 : $i, X43 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C_1 @ X42) @ (k2_relat_1 @ X42))
% 0.21/0.48          | ~ (r2_hidden @ X43 @ (k1_relat_1 @ X42))
% 0.21/0.48          | ~ (v1_relat_1 @ X42))),
% 0.21/0.48      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | (r2_hidden @ (sk_C_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (((r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.48        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.48        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['7', '12'])).
% 0.21/0.48  thf(t113_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X25 : $i, X26 : $i]:
% 0.21/0.48         (((k2_zfmisc_1 @ X25 @ X26) = (k1_xboole_0))
% 0.21/0.48          | ((X25) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X26 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X26) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.48  thf(fc6_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X40 : $i, X41 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X40 @ X41))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.48  thf('17', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.48      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (((r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.48        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['13', '17'])).
% 0.21/0.48  thf(t60_relat_1, conjecture,
% 0.21/0.48    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.48     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.48        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['19'])).
% 0.21/0.48  thf('21', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['19'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain, ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.21/0.48       ~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.48      inference('split', [status(esa)], ['19'])).
% 0.21/0.48  thf('26', plain, (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['24', '25'])).
% 0.21/0.48  thf('27', plain, (((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['20', '26'])).
% 0.21/0.48  thf('28', plain, ((r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['18', '27'])).
% 0.21/0.48  thf('29', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.48  thf('30', plain, ($false), inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
