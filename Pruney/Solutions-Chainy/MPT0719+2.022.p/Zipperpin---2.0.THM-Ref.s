%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ehop7iNwp2

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 (  57 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  254 ( 298 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X5 ) @ ( k1_relat_1 @ X4 ) )
      | ( v5_funct_1 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('12',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t142_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X7 ) )
      | ( ( k10_relat_1 @ X7 @ ( k1_tarski @ X8 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t172_relat_1,axiom,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X2: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t172_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0 != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','20'])).

thf(t174_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( v5_funct_1 @ k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( v5_funct_1 @ k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t174_funct_1])).

thf('22',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['23','24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ehop7iNwp2
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 18 iterations in 0.013s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.47  thf(cc1_relat_1, axiom,
% 0.19/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.19/0.47  thf('0', plain, (![X1 : $i]: ((v1_relat_1 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.19/0.47  thf(cc1_funct_1, axiom,
% 0.19/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.19/0.47  thf('1', plain, (![X3 : $i]: ((v1_funct_1 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.19/0.47  thf(t60_relat_1, axiom,
% 0.19/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.47  thf('2', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.47  thf(d20_funct_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.47           ( ( v5_funct_1 @ B @ A ) <=>
% 0.19/0.47             ( ![C:$i]:
% 0.19/0.47               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.47                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i]:
% 0.19/0.47         (~ (v1_relat_1 @ X4)
% 0.19/0.47          | ~ (v1_funct_1 @ X4)
% 0.19/0.47          | (r2_hidden @ (sk_C @ X4 @ X5) @ (k1_relat_1 @ X4))
% 0.19/0.47          | (v5_funct_1 @ X4 @ X5)
% 0.19/0.47          | ~ (v1_funct_1 @ X5)
% 0.19/0.47          | ~ (v1_relat_1 @ X5))),
% 0.19/0.47      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.19/0.47          | ~ (v1_relat_1 @ X0)
% 0.19/0.47          | ~ (v1_funct_1 @ X0)
% 0.19/0.47          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.19/0.47          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.19/0.47          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.47          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.47          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.19/0.47          | ~ (v1_funct_1 @ X0)
% 0.19/0.47          | ~ (v1_relat_1 @ X0)
% 0.19/0.47          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['1', '4'])).
% 0.19/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.47  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.47          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.19/0.47          | ~ (v1_funct_1 @ X0)
% 0.19/0.47          | ~ (v1_relat_1 @ X0)
% 0.19/0.47          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.47          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.19/0.47          | ~ (v1_relat_1 @ X0)
% 0.19/0.47          | ~ (v1_funct_1 @ X0)
% 0.19/0.47          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '7'])).
% 0.19/0.47  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.19/0.47          | ~ (v1_relat_1 @ X0)
% 0.19/0.47          | ~ (v1_funct_1 @ X0)
% 0.19/0.47          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.19/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf('11', plain, (![X1 : $i]: ((v1_relat_1 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.19/0.47  thf('12', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.47  thf(t142_funct_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ B ) =>
% 0.19/0.47       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.19/0.47         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X7 : $i, X8 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X8 @ (k2_relat_1 @ X7))
% 0.19/0.47          | ((k10_relat_1 @ X7 @ (k1_tarski @ X8)) != (k1_xboole_0))
% 0.19/0.47          | ~ (v1_relat_1 @ X7))),
% 0.19/0.47      inference('cnf', [status(esa)], [t142_funct_1])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.19/0.47          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.47          | ((k10_relat_1 @ k1_xboole_0 @ (k1_tarski @ X0)) != (k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.47  thf(t172_relat_1, axiom,
% 0.19/0.47    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X2 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t172_relat_1])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.19/0.47          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.47          | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.19/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_relat_1 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['16'])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['11', '17'])).
% 0.19/0.47  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.47  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.19/0.47          | ~ (v1_funct_1 @ X0)
% 0.19/0.47          | ~ (v1_relat_1 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['10', '20'])).
% 0.19/0.47  thf(t174_funct_1, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.47       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.47          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.19/0.47  thf('22', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('23', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.47  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('25', plain, ((v1_funct_1 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('26', plain, ($false),
% 0.19/0.47      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
