%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PZdgZZh1au

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  222 ( 296 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
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

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( r2_hidden @ ( sk_C_2 @ X12 @ X13 ) @ ( k1_relat_1 @ X12 ) )
      | ( v5_funct_1 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ X8 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
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

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('9',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

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

thf('17',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['18','19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PZdgZZh1au
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:19:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.34  % Number of cores: 8
% 0.18/0.34  % Python version: Python 3.6.8
% 0.18/0.34  % Running in FO mode
% 0.20/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.43  % Solved by: fo/fo7.sh
% 0.20/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.43  % done 24 iterations in 0.017s
% 0.20/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.43  % SZS output start Refutation
% 0.20/0.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.43  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.43  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.43  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.20/0.43  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.43  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.43  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.20/0.43  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.43  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.43  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.43  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.43  thf(cc1_funct_1, axiom,
% 0.20/0.43    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.20/0.43  thf('0', plain, (![X11 : $i]: ((v1_funct_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.20/0.43      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.20/0.43  thf(t60_relat_1, axiom,
% 0.20/0.43    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.43     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.43  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.43      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.43  thf(d20_funct_1, axiom,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.43       ( ![B:$i]:
% 0.20/0.43         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.43           ( ( v5_funct_1 @ B @ A ) <=>
% 0.20/0.43             ( ![C:$i]:
% 0.20/0.43               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.43                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.43  thf('2', plain,
% 0.20/0.43      (![X12 : $i, X13 : $i]:
% 0.20/0.43         (~ (v1_relat_1 @ X12)
% 0.20/0.43          | ~ (v1_funct_1 @ X12)
% 0.20/0.43          | (r2_hidden @ (sk_C_2 @ X12 @ X13) @ (k1_relat_1 @ X12))
% 0.20/0.43          | (v5_funct_1 @ X12 @ X13)
% 0.20/0.43          | ~ (v1_funct_1 @ X13)
% 0.20/0.43          | ~ (v1_relat_1 @ X13))),
% 0.20/0.43      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.20/0.43  thf('3', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r2_hidden @ (sk_C_2 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.20/0.43          | ~ (v1_relat_1 @ X0)
% 0.20/0.43          | ~ (v1_funct_1 @ X0)
% 0.20/0.43          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.20/0.43          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.43          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.43      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.43  thf(d1_relat_1, axiom,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( v1_relat_1 @ A ) <=>
% 0.20/0.43       ( ![B:$i]:
% 0.20/0.43         ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.43              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.43  thf('4', plain,
% 0.20/0.43      (![X8 : $i]: ((v1_relat_1 @ X8) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.20/0.43      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.20/0.43  thf(t2_boole, axiom,
% 0.20/0.43    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.43  thf('5', plain,
% 0.20/0.43      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.43      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.43  thf(t4_xboole_0, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.43            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.43       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.43            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.43  thf('6', plain,
% 0.20/0.43      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.43         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.20/0.43          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.43      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.43  thf('7', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]:
% 0.20/0.43         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.43  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.43  thf('8', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.20/0.43      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.43  thf('9', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.43      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.43  thf('10', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.43      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.43  thf('11', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r2_hidden @ (sk_C_2 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.20/0.43          | ~ (v1_relat_1 @ X0)
% 0.20/0.43          | ~ (v1_funct_1 @ X0)
% 0.20/0.43          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.20/0.43          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.20/0.43      inference('demod', [status(thm)], ['3', '10'])).
% 0.20/0.43  thf('12', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.43          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.20/0.43          | ~ (v1_funct_1 @ X0)
% 0.20/0.43          | ~ (v1_relat_1 @ X0)
% 0.20/0.43          | (r2_hidden @ (sk_C_2 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['0', '11'])).
% 0.20/0.43  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.43  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.43  thf('14', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.20/0.43          | ~ (v1_funct_1 @ X0)
% 0.20/0.43          | ~ (v1_relat_1 @ X0)
% 0.20/0.43          | (r2_hidden @ (sk_C_2 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.20/0.43      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.43  thf('15', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.43      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.43  thf('16', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         (~ (v1_relat_1 @ X0)
% 0.20/0.43          | ~ (v1_funct_1 @ X0)
% 0.20/0.43          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.43  thf(t174_funct_1, conjecture,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.43       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.20/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.43    (~( ![A:$i]:
% 0.20/0.43        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.43          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.20/0.43    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.20/0.43  thf('17', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('18', plain, ((~ (v1_funct_1 @ sk_A) | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.43      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.43  thf('19', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('20', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('21', plain, ($false),
% 0.20/0.43      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.43  
% 0.20/0.43  % SZS output end Refutation
% 0.20/0.43  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
