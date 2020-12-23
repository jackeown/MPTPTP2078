%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cJULgHKZON

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:53 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   45 (  66 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  348 ( 740 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t73_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
            & ( r2_hidden @ A @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_funct_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X14 @ X13 ) @ X12 )
        = ( k1_funct_1 @ X14 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t72_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('6',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X6: $i,X8: $i,X9: $i] :
      ( ( X6
       != ( k2_relat_1 @ X4 ) )
      | ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X4 ) )
      | ( X8
       != ( k1_funct_1 @ X4 @ X9 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('14',plain,(
    ! [X4: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X4 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X4 @ X9 ) @ ( k2_relat_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['3','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cJULgHKZON
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:35:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.73  % Solved by: fo/fo7.sh
% 0.53/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.73  % done 121 iterations in 0.279s
% 0.53/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.73  % SZS output start Refutation
% 0.53/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.73  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.53/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.53/0.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.53/0.73  thf(t73_funct_1, conjecture,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.53/0.73       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) =>
% 0.53/0.73         ( r2_hidden @
% 0.53/0.73           ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ))).
% 0.53/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.73        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.53/0.73          ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) =>
% 0.53/0.73            ( r2_hidden @
% 0.53/0.73              ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) )),
% 0.53/0.73    inference('cnf.neg', [status(esa)], [t73_funct_1])).
% 0.53/0.73  thf('0', plain,
% 0.53/0.73      (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ 
% 0.53/0.73          (k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_B)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(t72_funct_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.53/0.73       ( ( r2_hidden @ A @ B ) =>
% 0.53/0.73         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.53/0.73  thf('2', plain,
% 0.53/0.73      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.53/0.73         (~ (r2_hidden @ X12 @ X13)
% 0.53/0.73          | ~ (v1_relat_1 @ X14)
% 0.53/0.73          | ~ (v1_funct_1 @ X14)
% 0.53/0.73          | ((k1_funct_1 @ (k7_relat_1 @ X14 @ X13) @ X12)
% 0.53/0.73              = (k1_funct_1 @ X14 @ X12)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t72_funct_1])).
% 0.53/0.73  thf('3', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.53/0.73            = (k1_funct_1 @ X0 @ sk_A))
% 0.53/0.73          | ~ (v1_funct_1 @ X0)
% 0.53/0.73          | ~ (v1_relat_1 @ X0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.73  thf(fc8_funct_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.53/0.73       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.53/0.73         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.53/0.73  thf('4', plain,
% 0.53/0.73      (![X10 : $i, X11 : $i]:
% 0.53/0.73         (~ (v1_funct_1 @ X10)
% 0.53/0.73          | ~ (v1_relat_1 @ X10)
% 0.53/0.73          | (v1_relat_1 @ (k7_relat_1 @ X10 @ X11)))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.53/0.73  thf('5', plain,
% 0.53/0.73      (![X10 : $i, X11 : $i]:
% 0.53/0.73         (~ (v1_funct_1 @ X10)
% 0.53/0.73          | ~ (v1_relat_1 @ X10)
% 0.53/0.73          | (v1_funct_1 @ (k7_relat_1 @ X10 @ X11)))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.53/0.73  thf('6', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('7', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(t86_relat_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( v1_relat_1 @ C ) =>
% 0.53/0.73       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.53/0.73         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.53/0.73  thf('8', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         (~ (r2_hidden @ X0 @ X1)
% 0.53/0.73          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ X2))
% 0.53/0.73          | (r2_hidden @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X2 @ X1)))
% 0.53/0.73          | ~ (v1_relat_1 @ X2))),
% 0.53/0.73      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.53/0.73  thf('9', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ sk_C_1)
% 0.53/0.73          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ X0)))
% 0.53/0.73          | ~ (r2_hidden @ sk_A @ X0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.73  thf('10', plain, ((v1_relat_1 @ sk_C_1)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('11', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ X0)))
% 0.53/0.73          | ~ (r2_hidden @ sk_A @ X0))),
% 0.53/0.73      inference('demod', [status(thm)], ['9', '10'])).
% 0.53/0.73  thf('12', plain,
% 0.53/0.73      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_B)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['6', '11'])).
% 0.53/0.73  thf(d5_funct_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.53/0.73           ( ![C:$i]:
% 0.53/0.73             ( ( r2_hidden @ C @ B ) <=>
% 0.53/0.73               ( ?[D:$i]:
% 0.53/0.73                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.53/0.73                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.53/0.73  thf('13', plain,
% 0.53/0.73      (![X4 : $i, X6 : $i, X8 : $i, X9 : $i]:
% 0.53/0.73         (((X6) != (k2_relat_1 @ X4))
% 0.53/0.73          | (r2_hidden @ X8 @ X6)
% 0.53/0.73          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X4))
% 0.53/0.73          | ((X8) != (k1_funct_1 @ X4 @ X9))
% 0.53/0.73          | ~ (v1_funct_1 @ X4)
% 0.53/0.73          | ~ (v1_relat_1 @ X4))),
% 0.53/0.73      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.53/0.73  thf('14', plain,
% 0.53/0.73      (![X4 : $i, X9 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X4)
% 0.53/0.73          | ~ (v1_funct_1 @ X4)
% 0.53/0.73          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X4))
% 0.53/0.73          | (r2_hidden @ (k1_funct_1 @ X4 @ X9) @ (k2_relat_1 @ X4)))),
% 0.53/0.73      inference('simplify', [status(thm)], ['13'])).
% 0.53/0.73  thf('15', plain,
% 0.53/0.73      (((r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B) @ sk_A) @ 
% 0.53/0.73         (k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_B)))
% 0.53/0.73        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B))
% 0.53/0.73        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_B)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['12', '14'])).
% 0.53/0.73  thf('16', plain,
% 0.53/0.73      ((~ (v1_relat_1 @ sk_C_1)
% 0.53/0.73        | ~ (v1_funct_1 @ sk_C_1)
% 0.53/0.73        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_B))
% 0.53/0.73        | (r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B) @ sk_A) @ 
% 0.53/0.73           (k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_B))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['5', '15'])).
% 0.53/0.73  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('18', plain, ((v1_funct_1 @ sk_C_1)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('19', plain,
% 0.53/0.73      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_B))
% 0.53/0.73        | (r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B) @ sk_A) @ 
% 0.53/0.73           (k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_B))))),
% 0.53/0.73      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.53/0.73  thf('20', plain,
% 0.53/0.73      ((~ (v1_relat_1 @ sk_C_1)
% 0.53/0.73        | ~ (v1_funct_1 @ sk_C_1)
% 0.53/0.73        | (r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B) @ sk_A) @ 
% 0.53/0.73           (k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_B))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['4', '19'])).
% 0.53/0.73  thf('21', plain, ((v1_relat_1 @ sk_C_1)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('22', plain, ((v1_funct_1 @ sk_C_1)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('23', plain,
% 0.53/0.73      ((r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B) @ sk_A) @ 
% 0.53/0.73        (k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_B)))),
% 0.53/0.73      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.53/0.73  thf('24', plain,
% 0.53/0.73      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ 
% 0.53/0.73         (k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_B)))
% 0.53/0.73        | ~ (v1_relat_1 @ sk_C_1)
% 0.53/0.73        | ~ (v1_funct_1 @ sk_C_1))),
% 0.53/0.73      inference('sup+', [status(thm)], ['3', '23'])).
% 0.53/0.73  thf('25', plain, ((v1_relat_1 @ sk_C_1)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('26', plain, ((v1_funct_1 @ sk_C_1)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('27', plain,
% 0.53/0.73      ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ 
% 0.53/0.73        (k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_B)))),
% 0.53/0.73      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.53/0.73  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.53/0.73  
% 0.53/0.73  % SZS output end Refutation
% 0.53/0.73  
% 0.53/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
