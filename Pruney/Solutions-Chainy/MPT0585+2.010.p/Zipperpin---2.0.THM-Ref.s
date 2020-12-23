%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IgqGa4QNxw

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:28 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   45 (  52 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :   14
%              Number of atoms          :  412 ( 507 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) @ X26 )
        = ( k7_relat_1 @ X24 @ ( k3_xboole_0 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) ) )
      | ( r2_hidden @ X27 @ ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('11',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ( ( k7_relat_1 @ X32 @ X33 )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t189_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
              = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t189_relat_1])).

thf('20',plain,(
    ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
 != ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
     != ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
 != ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
     != ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
 != ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IgqGa4QNxw
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:25:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.60/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.82  % Solved by: fo/fo7.sh
% 0.60/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.82  % done 482 iterations in 0.372s
% 0.60/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.82  % SZS output start Refutation
% 0.60/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.60/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.82  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.60/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.82  thf(t100_relat_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ C ) =>
% 0.60/0.82       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.60/0.82         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.60/0.82  thf('0', plain,
% 0.60/0.82      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.60/0.82         (((k7_relat_1 @ (k7_relat_1 @ X24 @ X25) @ X26)
% 0.60/0.82            = (k7_relat_1 @ X24 @ (k3_xboole_0 @ X25 @ X26)))
% 0.60/0.82          | ~ (v1_relat_1 @ X24))),
% 0.60/0.82      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.60/0.82  thf(d3_tarski, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( r1_tarski @ A @ B ) <=>
% 0.60/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.60/0.82  thf('1', plain,
% 0.60/0.82      (![X1 : $i, X3 : $i]:
% 0.60/0.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.60/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.82  thf(t90_relat_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ B ) =>
% 0.60/0.82       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.60/0.82         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.60/0.82  thf('2', plain,
% 0.60/0.82      (![X30 : $i, X31 : $i]:
% 0.60/0.82         (((k1_relat_1 @ (k7_relat_1 @ X30 @ X31))
% 0.60/0.82            = (k3_xboole_0 @ (k1_relat_1 @ X30) @ X31))
% 0.60/0.82          | ~ (v1_relat_1 @ X30))),
% 0.60/0.82      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.60/0.82  thf(t86_relat_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ C ) =>
% 0.60/0.82       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.60/0.82         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.60/0.82  thf('3', plain,
% 0.60/0.82      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X27 @ (k1_relat_1 @ (k7_relat_1 @ X29 @ X28)))
% 0.60/0.82          | (r2_hidden @ X27 @ (k1_relat_1 @ X29))
% 0.60/0.82          | ~ (v1_relat_1 @ X29))),
% 0.60/0.82      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.60/0.82  thf('4', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.60/0.82          | ~ (v1_relat_1 @ X1)
% 0.60/0.82          | ~ (v1_relat_1 @ X1)
% 0.60/0.82          | (r2_hidden @ X2 @ (k1_relat_1 @ X1)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.82  thf('5', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.82         ((r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 0.60/0.82          | ~ (v1_relat_1 @ X1)
% 0.60/0.82          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.60/0.82      inference('simplify', [status(thm)], ['4'])).
% 0.60/0.82  thf('6', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.82         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2)
% 0.60/0.82          | ~ (v1_relat_1 @ X1)
% 0.60/0.82          | (r2_hidden @ 
% 0.60/0.82             (sk_C @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)) @ 
% 0.60/0.82             (k1_relat_1 @ X1)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['1', '5'])).
% 0.60/0.82  thf('7', plain,
% 0.60/0.82      (![X1 : $i, X3 : $i]:
% 0.60/0.82         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.60/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.82  thf('8', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X0)
% 0.60/0.82          | (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.60/0.82             (k1_relat_1 @ X0))
% 0.60/0.82          | (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.60/0.82             (k1_relat_1 @ X0)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.82  thf('9', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.60/0.82           (k1_relat_1 @ X0))
% 0.60/0.82          | ~ (v1_relat_1 @ X0))),
% 0.60/0.82      inference('simplify', [status(thm)], ['8'])).
% 0.60/0.82  thf('10', plain,
% 0.60/0.82      (![X30 : $i, X31 : $i]:
% 0.60/0.82         (((k1_relat_1 @ (k7_relat_1 @ X30 @ X31))
% 0.60/0.82            = (k3_xboole_0 @ (k1_relat_1 @ X30) @ X31))
% 0.60/0.82          | ~ (v1_relat_1 @ X30))),
% 0.60/0.82      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.60/0.82  thf(t97_relat_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ B ) =>
% 0.60/0.82       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.60/0.82         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.60/0.82  thf('11', plain,
% 0.60/0.82      (![X32 : $i, X33 : $i]:
% 0.60/0.82         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 0.60/0.82          | ((k7_relat_1 @ X32 @ X33) = (X32))
% 0.60/0.82          | ~ (v1_relat_1 @ X32))),
% 0.60/0.82      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.60/0.82  thf('12', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.82         (~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2)
% 0.60/0.82          | ~ (v1_relat_1 @ X1)
% 0.60/0.82          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.60/0.82          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.60/0.82              = (k7_relat_1 @ X1 @ X0)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.82  thf('13', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X0)
% 0.60/0.82          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.60/0.82              = (k7_relat_1 @ X0 @ X1))
% 0.60/0.82          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.60/0.82          | ~ (v1_relat_1 @ X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['9', '12'])).
% 0.60/0.82  thf('14', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.60/0.82          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.60/0.82              = (k7_relat_1 @ X0 @ X1))
% 0.60/0.82          | ~ (v1_relat_1 @ X0))),
% 0.60/0.82      inference('simplify', [status(thm)], ['13'])).
% 0.60/0.82  thf(dt_k7_relat_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.60/0.82  thf('15', plain,
% 0.60/0.82      (![X22 : $i, X23 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X22) | (v1_relat_1 @ (k7_relat_1 @ X22 @ X23)))),
% 0.60/0.82      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.60/0.82  thf('16', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X0)
% 0.60/0.82          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.60/0.82              = (k7_relat_1 @ X0 @ X1)))),
% 0.60/0.82      inference('clc', [status(thm)], ['14', '15'])).
% 0.60/0.82  thf('17', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         (((k7_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.60/0.82            = (k7_relat_1 @ X0 @ X1))
% 0.60/0.82          | ~ (v1_relat_1 @ X0)
% 0.60/0.82          | ~ (v1_relat_1 @ X0))),
% 0.60/0.82      inference('sup+', [status(thm)], ['0', '16'])).
% 0.60/0.82  thf('18', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X0)
% 0.60/0.82          | ((k7_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.60/0.82              = (k7_relat_1 @ X0 @ X1)))),
% 0.60/0.82      inference('simplify', [status(thm)], ['17'])).
% 0.60/0.82  thf('19', plain,
% 0.60/0.82      (![X30 : $i, X31 : $i]:
% 0.60/0.82         (((k1_relat_1 @ (k7_relat_1 @ X30 @ X31))
% 0.60/0.82            = (k3_xboole_0 @ (k1_relat_1 @ X30) @ X31))
% 0.60/0.82          | ~ (v1_relat_1 @ X30))),
% 0.60/0.82      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.60/0.82  thf(t189_relat_1, conjecture,
% 0.60/0.82    (![A:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ A ) =>
% 0.60/0.82       ( ![B:$i]:
% 0.60/0.82         ( ( v1_relat_1 @ B ) =>
% 0.60/0.82           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 0.60/0.82             ( k7_relat_1 @
% 0.60/0.82               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.60/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.82    (~( ![A:$i]:
% 0.60/0.82        ( ( v1_relat_1 @ A ) =>
% 0.60/0.82          ( ![B:$i]:
% 0.60/0.82            ( ( v1_relat_1 @ B ) =>
% 0.60/0.82              ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 0.60/0.82                ( k7_relat_1 @
% 0.60/0.82                  A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) )),
% 0.60/0.82    inference('cnf.neg', [status(esa)], [t189_relat_1])).
% 0.60/0.82  thf('20', plain,
% 0.60/0.82      (((k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.60/0.82         != (k7_relat_1 @ sk_A @ 
% 0.60/0.82             (k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('21', plain,
% 0.60/0.82      ((((k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.60/0.82          != (k7_relat_1 @ sk_A @ 
% 0.60/0.82              (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))))
% 0.60/0.82        | ~ (v1_relat_1 @ sk_B))),
% 0.60/0.82      inference('sup-', [status(thm)], ['19', '20'])).
% 0.60/0.82  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('23', plain,
% 0.60/0.82      (((k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.60/0.82         != (k7_relat_1 @ sk_A @ 
% 0.60/0.82             (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))))),
% 0.60/0.82      inference('demod', [status(thm)], ['21', '22'])).
% 0.60/0.82  thf('24', plain,
% 0.60/0.82      ((((k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.60/0.82          != (k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.60/0.82        | ~ (v1_relat_1 @ sk_A))),
% 0.60/0.82      inference('sup-', [status(thm)], ['18', '23'])).
% 0.60/0.82  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('26', plain,
% 0.60/0.82      (((k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.60/0.82         != (k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.60/0.82      inference('demod', [status(thm)], ['24', '25'])).
% 0.60/0.82  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.60/0.82  
% 0.60/0.82  % SZS output end Refutation
% 0.60/0.82  
% 0.60/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
