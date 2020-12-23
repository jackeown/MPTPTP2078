%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.piXOvKQBmJ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  88 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  468 ( 960 expanded)
%              Number of equality atoms :   18 (  39 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X34 @ X35 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ ( k7_relat_1 @ X33 @ X32 ) ) )
      | ( r2_hidden @ X31 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X34 @ X35 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('10',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ ( k7_relat_1 @ X33 @ X32 ) ) )
      | ( r2_hidden @ X31 @ ( k1_relat_1 @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ X33 ) )
      | ( r2_hidden @ X31 @ ( k1_relat_1 @ ( k7_relat_1 @ X33 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('21',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X36 ) @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

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

thf('22',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ~ ( v1_funct_1 @ X40 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X40 @ X41 ) @ X42 )
        = ( k1_funct_1 @ X41 @ ( k1_funct_1 @ X40 @ X42 ) ) )
      | ~ ( r2_hidden @ X42 @ ( k1_relat_1 @ ( k5_relat_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X39: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['5','6'])).

thf(t35_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A )
        = A ) ) )).

thf('32',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ X44 ) @ X43 )
        = X43 )
      | ~ ( r2_hidden @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_1])).

thf('33',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) @ sk_A )
    = ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30','33'])).

thf('35',plain,(
    ( k1_funct_1 @ sk_C @ sk_A )
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.piXOvKQBmJ
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 54 iterations in 0.030s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(t38_funct_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.20/0.48         ( ( k1_funct_1 @ C @ A ) =
% 0.20/0.48           ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.20/0.48            ( ( k1_funct_1 @ C @ A ) =
% 0.20/0.48              ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t38_funct_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t90_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.20/0.48         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X34 : $i, X35 : $i]:
% 0.20/0.48         (((k1_relat_1 @ (k7_relat_1 @ X34 @ X35))
% 0.20/0.48            = (k3_xboole_0 @ (k1_relat_1 @ X34) @ X35))
% 0.20/0.48          | ~ (v1_relat_1 @ X34))),
% 0.20/0.48      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.20/0.48  thf(t86_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ C ) =>
% 0.20/0.48       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.20/0.48         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X31 @ (k1_relat_1 @ (k7_relat_1 @ X33 @ X32)))
% 0.20/0.48          | (r2_hidden @ X31 @ X32)
% 0.20/0.48          | ~ (v1_relat_1 @ X33))),
% 0.20/0.48      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | (r2_hidden @ X2 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((r2_hidden @ X2 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.48  thf('5', plain, ((~ (v1_relat_1 @ sk_C) | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '4'])).
% 0.20/0.48  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X34 : $i, X35 : $i]:
% 0.20/0.48         (((k1_relat_1 @ (k7_relat_1 @ X34 @ X35))
% 0.20/0.48            = (k3_xboole_0 @ (k1_relat_1 @ X34) @ X35))
% 0.20/0.48          | ~ (v1_relat_1 @ X34))),
% 0.20/0.48      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X31 @ (k1_relat_1 @ (k7_relat_1 @ X33 @ X32)))
% 0.20/0.48          | (r2_hidden @ X31 @ (k1_relat_1 @ X33))
% 0.20/0.48          | ~ (v1_relat_1 @ X33))),
% 0.20/0.48      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | (r2_hidden @ X2 @ (k1_relat_1 @ X1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_C) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '12'])).
% 0.20/0.48  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X31 @ X32)
% 0.20/0.48          | ~ (r2_hidden @ X31 @ (k1_relat_1 @ X33))
% 0.20/0.48          | (r2_hidden @ X31 @ (k1_relat_1 @ (k7_relat_1 @ X33 @ X32)))
% 0.20/0.48          | ~ (v1_relat_1 @ X33))),
% 0.20/0.48      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ sk_C)
% 0.20/0.48          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ X0)))
% 0.20/0.48          | ~ (r2_hidden @ sk_A @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ X0)))
% 0.20/0.48          | ~ (r2_hidden @ sk_A @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '19'])).
% 0.20/0.48  thf(t94_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X36 : $i, X37 : $i]:
% 0.20/0.48         (((k7_relat_1 @ X37 @ X36) = (k5_relat_1 @ (k6_relat_1 @ X36) @ X37))
% 0.20/0.48          | ~ (v1_relat_1 @ X37))),
% 0.20/0.48      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.48  thf(t22_funct_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.20/0.48             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.20/0.48               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X40)
% 0.20/0.48          | ~ (v1_funct_1 @ X40)
% 0.20/0.48          | ((k1_funct_1 @ (k5_relat_1 @ X40 @ X41) @ X42)
% 0.20/0.48              = (k1_funct_1 @ X41 @ (k1_funct_1 @ X40 @ X42)))
% 0.20/0.48          | ~ (r2_hidden @ X42 @ (k1_relat_1 @ (k5_relat_1 @ X40 @ X41)))
% 0.20/0.48          | ~ (v1_funct_1 @ X41)
% 0.20/0.48          | ~ (v1_relat_1 @ X41))),
% 0.20/0.48      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_funct_1 @ X1)
% 0.20/0.48          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2)
% 0.20/0.48              = (k1_funct_1 @ X1 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X2)))
% 0.20/0.48          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf(fc3_funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.48       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.48  thf('24', plain, (![X39 : $i]: (v1_funct_1 @ (k6_relat_1 @ X39))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.48  thf('25', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_funct_1 @ X1)
% 0.20/0.48          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2)
% 0.20/0.48              = (k1_funct_1 @ X1 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X2))))),
% 0.20/0.48      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2)
% 0.20/0.48            = (k1_funct_1 @ X1 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X2)))
% 0.20/0.48          | ~ (v1_funct_1 @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.48        | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) @ sk_A)
% 0.20/0.48            = (k1_funct_1 @ sk_C @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['20', '27'])).
% 0.20/0.48  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(t35_funct_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.48       ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A ) = ( A ) ) ))).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X43 : $i, X44 : $i]:
% 0.20/0.48         (((k1_funct_1 @ (k6_relat_1 @ X44) @ X43) = (X43))
% 0.20/0.48          | ~ (r2_hidden @ X43 @ X44))),
% 0.20/0.48      inference('cnf', [status(esa)], [t35_funct_1])).
% 0.20/0.48  thf('33', plain, (((k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A) = (sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) @ sk_A)
% 0.20/0.48         = (k1_funct_1 @ sk_C @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['28', '29', '30', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (((k1_funct_1 @ sk_C @ sk_A)
% 0.20/0.48         != (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('36', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
