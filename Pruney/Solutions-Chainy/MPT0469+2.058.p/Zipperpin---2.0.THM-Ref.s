%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h4aCD7DlPl

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  68 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  212 ( 398 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('0',plain,(
    ! [X22: $i,X25: $i] :
      ( ( X25
        = ( k2_relat_1 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ X25 @ X22 ) @ ( sk_C_3 @ X25 @ X22 ) ) @ X22 )
      | ( r2_hidden @ ( sk_C_3 @ X25 @ X22 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('5',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('8',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

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

thf('9',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18
        = ( k1_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X18 @ X15 ) @ ( sk_D_2 @ X18 @ X15 ) ) @ X15 )
      | ( r2_hidden @ ( sk_C_2 @ X18 @ X15 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('12',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('15',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('17',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('20',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['10','20'])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h4aCD7DlPl
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:27:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 46 iterations in 0.035s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.20/0.48  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.20/0.48  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i).
% 0.20/0.48  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.20/0.48  thf(d5_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X22 : $i, X25 : $i]:
% 0.20/0.48         (((X25) = (k2_relat_1 @ X22))
% 0.20/0.48          | (r2_hidden @ 
% 0.20/0.48             (k4_tarski @ (sk_D_4 @ X25 @ X22) @ (sk_C_3 @ X25 @ X22)) @ X22)
% 0.20/0.48          | (r2_hidden @ (sk_C_3 @ X25 @ X22) @ X25))),
% 0.20/0.48      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.48  thf(t2_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.48  thf(t4_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.20/0.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.48  thf('4', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.20/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.48  thf('5', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 0.20/0.48          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.48  thf('7', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('8', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf(t60_relat_1, conjecture,
% 0.20/0.48    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.48     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.48        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.48         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['9'])).
% 0.20/0.48  thf(d4_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X15 : $i, X18 : $i]:
% 0.20/0.48         (((X18) = (k1_relat_1 @ X15))
% 0.20/0.48          | (r2_hidden @ 
% 0.20/0.48             (k4_tarski @ (sk_C_2 @ X18 @ X15) @ (sk_D_2 @ X18 @ X15)) @ X15)
% 0.20/0.48          | (r2_hidden @ (sk_C_2 @ X18 @ X15) @ X18))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.48  thf('12', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.20/0.48          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('15', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.48         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['9'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.48         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.20/0.48       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.48      inference('split', [status(esa)], ['9'])).
% 0.20/0.48  thf('20', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['10', '20'])).
% 0.20/0.48  thf('22', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['8', '21'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
