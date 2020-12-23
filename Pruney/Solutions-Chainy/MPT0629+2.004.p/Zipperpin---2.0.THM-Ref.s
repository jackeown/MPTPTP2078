%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u8Sw1x8Bk4

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   23 (  29 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :  117 ( 225 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t25_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
             => ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_funct_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) ) @ ( k2_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ ( k2_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    $false ),
    inference(demod,[status(thm)],['0','8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u8Sw1x8Bk4
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:44:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 12 iterations in 0.011s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.45  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(t25_funct_1, conjecture,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.45       ( ![C:$i]:
% 0.19/0.45         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.45           ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.19/0.45             ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i,B:$i]:
% 0.19/0.45        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.45          ( ![C:$i]:
% 0.19/0.45            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.45              ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.19/0.45                ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t25_funct_1])).
% 0.19/0.45  thf('0', plain, (~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      ((r2_hidden @ sk_A @ (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t45_relat_1, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( v1_relat_1 @ A ) =>
% 0.19/0.45       ( ![B:$i]:
% 0.19/0.45         ( ( v1_relat_1 @ B ) =>
% 0.19/0.45           ( r1_tarski @
% 0.19/0.45             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      (![X4 : $i, X5 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X4)
% 0.19/0.45          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X5 @ X4)) @ 
% 0.19/0.45             (k2_relat_1 @ X4))
% 0.19/0.45          | ~ (v1_relat_1 @ X5))),
% 0.19/0.45      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.19/0.45  thf(d3_tarski, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.45  thf('3', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.45          | (r2_hidden @ X0 @ X2)
% 0.19/0.45          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.45      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.45  thf('4', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X1)
% 0.19/0.45          | ~ (v1_relat_1 @ X0)
% 0.19/0.45          | (r2_hidden @ X2 @ (k2_relat_1 @ X0))
% 0.19/0.45          | ~ (r2_hidden @ X2 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.19/0.45      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.45  thf('5', plain,
% 0.19/0.45      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))
% 0.19/0.45        | ~ (v1_relat_1 @ sk_B)
% 0.19/0.45        | ~ (v1_relat_1 @ sk_C_1))),
% 0.19/0.45      inference('sup-', [status(thm)], ['1', '4'])).
% 0.19/0.45  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('7', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('8', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.19/0.45      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.19/0.45  thf('9', plain, ($false), inference('demod', [status(thm)], ['0', '8'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
