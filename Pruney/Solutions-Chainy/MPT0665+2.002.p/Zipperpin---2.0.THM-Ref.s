%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bZj3b0e0Kg

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  56 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  341 ( 575 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

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

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X14 ) @ X12 )
      | ( X14
       != ( k1_funct_1 @ X12 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ ( k1_funct_1 @ X12 @ X11 ) ) @ X12 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(d11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k7_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ D @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k7_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k7_relat_1 @ sk_C @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k7_relat_1 @ sk_C @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 )
      | ( r2_hidden @ X9 @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['22','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bZj3b0e0Kg
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:58:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 29 iterations in 0.024s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(dt_k7_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.48  thf(t73_funct_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) =>
% 0.20/0.48         ( r2_hidden @
% 0.20/0.48           ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48          ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) =>
% 0.20/0.48            ( r2_hidden @
% 0.20/0.48              ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t73_funct_1])).
% 0.20/0.48  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d4_funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48       ( ![B:$i,C:$i]:
% 0.20/0.48         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.20/0.48             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.20/0.48               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.48           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.48             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.20/0.48               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 0.20/0.48          | (r2_hidden @ (k4_tarski @ X11 @ X14) @ X12)
% 0.20/0.48          | ((X14) != (k1_funct_1 @ X12 @ X11))
% 0.20/0.48          | ~ (v1_funct_1 @ X12)
% 0.20/0.48          | ~ (v1_relat_1 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X12)
% 0.20/0.48          | ~ (v1_funct_1 @ X12)
% 0.20/0.48          | (r2_hidden @ (k4_tarski @ X11 @ (k1_funct_1 @ X12 @ X11)) @ X12)
% 0.20/0.48          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X12)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.48  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C)),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.48  thf(d11_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i,C:$i]:
% 0.20/0.48         ( ( v1_relat_1 @ C ) =>
% 0.20/0.48           ( ( ( C ) = ( k7_relat_1 @ A @ B ) ) <=>
% 0.20/0.48             ( ![D:$i,E:$i]:
% 0.20/0.48               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.20/0.48                 ( ( r2_hidden @ D @ B ) & 
% 0.20/0.48                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0)
% 0.20/0.48          | ((X0) != (k7_relat_1 @ X1 @ X2))
% 0.20/0.48          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X0)
% 0.20/0.48          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.20/0.48          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d11_relat_1])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.48          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.20/0.48          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ (k7_relat_1 @ X1 @ X2))
% 0.20/0.48          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X1)
% 0.20/0.48          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.48          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.20/0.48          | ~ (r2_hidden @ X3 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X3 @ X0)
% 0.20/0.48          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.20/0.48          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ sk_C)
% 0.20/0.48          | (r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.20/0.48             (k7_relat_1 @ sk_C @ X0))
% 0.20/0.48          | ~ (r2_hidden @ sk_A @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '13'])).
% 0.20/0.48  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.20/0.48           (k7_relat_1 @ sk_C @ X0))
% 0.20/0.48          | ~ (r2_hidden @ sk_A @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.20/0.48        (k7_relat_1 @ sk_C @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '16'])).
% 0.20/0.48  thf(t20_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ C ) =>
% 0.20/0.48       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.20/0.48         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.48           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         (~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10)
% 0.20/0.48          | (r2_hidden @ X9 @ (k2_relat_1 @ X10))
% 0.20/0.48          | ~ (v1_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))
% 0.20/0.48        | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ 
% 0.20/0.48           (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ 
% 0.20/0.48          (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain, (~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain, (~ (v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '21'])).
% 0.20/0.48  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain, ($false), inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
