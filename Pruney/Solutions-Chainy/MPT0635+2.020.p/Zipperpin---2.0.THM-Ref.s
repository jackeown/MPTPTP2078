%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CFywO14erA

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  65 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  437 ( 709 expanded)
%              Number of equality atoms :   19 (  32 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t38_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
       => ( ( k1_funct_1 @ C @ A )
          = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
         => ( ( k1_funct_1 @ C @ A )
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X44 ) @ X43 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X43 ) @ X44 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t37_funct_1])).

thf(t22_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ~ ( v1_funct_1 @ X38 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X38 @ X39 ) @ X40 )
        = ( k1_funct_1 @ X39 @ ( k1_funct_1 @ X38 @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ ( k1_relat_1 @ ( k5_relat_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X34: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X44 ) @ X43 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X43 ) @ X44 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t37_funct_1])).

thf(t21_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ ( k5_relat_1 @ X35 @ X37 ) ) )
      | ( r2_hidden @ X36 @ ( k1_relat_1 @ X35 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('15',plain,(
    ! [X31: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('16',plain,(
    ! [X34: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['20','21','22'])).

thf(t35_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A )
        = A ) ) )).

thf('24',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ X42 ) @ X41 )
        = X41 )
      | ~ ( r2_hidden @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_1])).

thf('25',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) @ sk_A )
    = ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10','25'])).

thf('27',plain,(
    ( k1_funct_1 @ sk_C @ sk_A )
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CFywO14erA
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:34:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 53 iterations in 0.034s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.50  thf(t38_funct_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.50       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.22/0.50         ( ( k1_funct_1 @ C @ A ) =
% 0.22/0.50           ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.50        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.50          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.22/0.50            ( ( k1_funct_1 @ C @ A ) =
% 0.22/0.50              ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t38_funct_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t37_funct_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.50       ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) =
% 0.22/0.50         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X43 : $i, X44 : $i]:
% 0.22/0.50         (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X44) @ X43))
% 0.22/0.50            = (k3_xboole_0 @ (k1_relat_1 @ X43) @ X44))
% 0.22/0.50          | ~ (v1_funct_1 @ X43)
% 0.22/0.50          | ~ (v1_relat_1 @ X43))),
% 0.22/0.50      inference('cnf', [status(esa)], [t37_funct_1])).
% 0.22/0.50  thf(t22_funct_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.50       ( ![C:$i]:
% 0.22/0.50         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.50           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.22/0.50             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.22/0.50               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X38)
% 0.22/0.50          | ~ (v1_funct_1 @ X38)
% 0.22/0.50          | ((k1_funct_1 @ (k5_relat_1 @ X38 @ X39) @ X40)
% 0.22/0.50              = (k1_funct_1 @ X39 @ (k1_funct_1 @ X38 @ X40)))
% 0.22/0.50          | ~ (r2_hidden @ X40 @ (k1_relat_1 @ (k5_relat_1 @ X38 @ X39)))
% 0.22/0.50          | ~ (v1_funct_1 @ X39)
% 0.22/0.50          | ~ (v1_relat_1 @ X39))),
% 0.22/0.50      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (v1_funct_1 @ X1)
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (v1_funct_1 @ X1)
% 0.22/0.50          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2)
% 0.22/0.50              = (k1_funct_1 @ X1 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X2)))
% 0.22/0.50          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf(fc3_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.50  thf('4', plain, (![X34 : $i]: (v1_funct_1 @ (k6_relat_1 @ X34))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.50  thf('5', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (v1_funct_1 @ X1)
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (v1_funct_1 @ X1)
% 0.22/0.50          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2)
% 0.22/0.50              = (k1_funct_1 @ X1 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X2))))),
% 0.22/0.50      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2)
% 0.22/0.50            = (k1_funct_1 @ X1 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X2)))
% 0.22/0.50          | ~ (v1_funct_1 @ X1)
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.50        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.50        | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) @ sk_A)
% 0.22/0.50            = (k1_funct_1 @ sk_C @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '7'])).
% 0.22/0.50  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X43 : $i, X44 : $i]:
% 0.22/0.50         (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X44) @ X43))
% 0.22/0.50            = (k3_xboole_0 @ (k1_relat_1 @ X43) @ X44))
% 0.22/0.50          | ~ (v1_funct_1 @ X43)
% 0.22/0.50          | ~ (v1_relat_1 @ X43))),
% 0.22/0.50      inference('cnf', [status(esa)], [t37_funct_1])).
% 0.22/0.50  thf(t21_funct_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.50       ( ![C:$i]:
% 0.22/0.50         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.50           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.22/0.50             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.50               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X35)
% 0.22/0.50          | ~ (v1_funct_1 @ X35)
% 0.22/0.50          | ~ (r2_hidden @ X36 @ (k1_relat_1 @ (k5_relat_1 @ X35 @ X37)))
% 0.22/0.50          | (r2_hidden @ X36 @ (k1_relat_1 @ X35))
% 0.22/0.50          | ~ (v1_funct_1 @ X37)
% 0.22/0.50          | ~ (v1_relat_1 @ X37))),
% 0.22/0.50      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (v1_funct_1 @ X1)
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (v1_funct_1 @ X1)
% 0.22/0.50          | (r2_hidden @ X2 @ (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.22/0.50          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf(t71_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.50  thf('15', plain, (![X31 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X31)) = (X31))),
% 0.22/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.50  thf('16', plain, (![X34 : $i]: (v1_funct_1 @ (k6_relat_1 @ X34))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.50  thf('17', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (v1_funct_1 @ X1)
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (v1_funct_1 @ X1)
% 0.22/0.50          | (r2_hidden @ X2 @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((r2_hidden @ X2 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X1)
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.50        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.50        | (r2_hidden @ sk_A @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '19'])).
% 0.22/0.50  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('23', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.50      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.22/0.50  thf(t35_funct_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r2_hidden @ A @ B ) =>
% 0.22/0.50       ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A ) = ( A ) ) ))).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X41 : $i, X42 : $i]:
% 0.22/0.50         (((k1_funct_1 @ (k6_relat_1 @ X42) @ X41) = (X41))
% 0.22/0.50          | ~ (r2_hidden @ X41 @ X42))),
% 0.22/0.50      inference('cnf', [status(esa)], [t35_funct_1])).
% 0.22/0.50  thf('25', plain, (((k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A) = (sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) @ sk_A)
% 0.22/0.50         = (k1_funct_1 @ sk_C @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['8', '9', '10', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (((k1_funct_1 @ sk_C @ sk_A)
% 0.22/0.50         != (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('28', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
