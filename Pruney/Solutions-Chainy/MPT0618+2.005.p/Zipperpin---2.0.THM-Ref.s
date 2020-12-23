%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QmhNjJjDJs

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  34 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  154 ( 266 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t12_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_funct_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X4 ) )
      | ( X5
       != ( k1_funct_1 @ X4 @ X3 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( k1_funct_1 @ X4 @ X3 ) ) @ X4 )
      | ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QmhNjJjDJs
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:07:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 9 iterations in 0.010s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(t12_funct_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.46       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.46         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.46          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.46            ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t12_funct_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t8_funct_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.46       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.46         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.46           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X3 @ (k1_relat_1 @ X4))
% 0.20/0.46          | ((X5) != (k1_funct_1 @ X4 @ X3))
% 0.20/0.46          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X4)
% 0.20/0.46          | ~ (v1_funct_1 @ X4)
% 0.20/0.46          | ~ (v1_relat_1 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X4)
% 0.20/0.46          | ~ (v1_funct_1 @ X4)
% 0.20/0.46          | (r2_hidden @ (k4_tarski @ X3 @ (k1_funct_1 @ X4 @ X3)) @ X4)
% 0.20/0.46          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ X4)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.20/0.46        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.46        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.46  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)),
% 0.20/0.46      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.46  thf(t20_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ C ) =>
% 0.20/0.46       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.20/0.46         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.46           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.20/0.46          | (r2_hidden @ X1 @ (k2_relat_1 @ X2))
% 0.20/0.46          | ~ (v1_relat_1 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.46        | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.46  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain, ($false), inference('demod', [status(thm)], ['0', '11'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
