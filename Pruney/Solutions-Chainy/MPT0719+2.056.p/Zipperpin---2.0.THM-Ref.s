%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LwAY9PNT5L

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:33 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 (  64 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  252 ( 417 expanded)
%              Number of equality atoms :   19 (  39 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(o_1_0_funct_1_type,type,(
    o_1_0_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,
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

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ ( k1_relat_1 @ X7 ) )
      | ( v5_funct_1 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(s3_funct_1__e1_27_1__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ B )
         => ( ( k1_funct_1 @ C @ D )
            = ( o_1_0_funct_1 @ A ) ) )
      & ( ( k1_relat_1 @ C )
        = B )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( ( ( k1_relat_1 @ X6 )
       != k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( ( sk_C_2 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_2 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf('10',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf('13',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','10','13'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,(
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

thf('16',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('18',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('19',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

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

thf('21',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['22','23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LwAY9PNT5L
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 24 iterations in 0.016s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.47  thf(o_1_0_funct_1_type, type, o_1_0_funct_1: $i > $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.19/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.47  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.19/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.47  thf(t60_relat_1, axiom,
% 0.19/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.47  thf('0', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
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
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X7 : $i, X8 : $i]:
% 0.19/0.47         (~ (v1_relat_1 @ X7)
% 0.19/0.47          | ~ (v1_funct_1 @ X7)
% 0.19/0.47          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ (k1_relat_1 @ X7))
% 0.19/0.47          | (v5_funct_1 @ X7 @ X8)
% 0.19/0.47          | ~ (v1_funct_1 @ X8)
% 0.19/0.47          | ~ (v1_relat_1 @ X8))),
% 0.19/0.47      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.19/0.47          | ~ (v1_relat_1 @ X0)
% 0.19/0.47          | ~ (v1_funct_1 @ X0)
% 0.19/0.47          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.19/0.47          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.19/0.47          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['0', '1'])).
% 0.19/0.47  thf(s3_funct_1__e1_27_1__funct_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ?[C:$i]:
% 0.19/0.47       ( ( ![D:$i]:
% 0.19/0.47           ( ( r2_hidden @ D @ B ) =>
% 0.19/0.47             ( ( k1_funct_1 @ C @ D ) = ( o_1_0_funct_1 @ A ) ) ) ) & 
% 0.19/0.47         ( ( k1_relat_1 @ C ) = ( B ) ) & ( v1_funct_1 @ C ) & 
% 0.19/0.47         ( v1_relat_1 @ C ) ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i]: ((k1_relat_1 @ (sk_C_2 @ X10 @ X11)) = (X10))),
% 0.19/0.47      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 0.19/0.47  thf(t64_relat_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ A ) =>
% 0.19/0.47       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.19/0.47           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.47         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X6 : $i]:
% 0.19/0.47         (((k1_relat_1 @ X6) != (k1_xboole_0))
% 0.19/0.47          | ((X6) = (k1_xboole_0))
% 0.19/0.47          | ~ (v1_relat_1 @ X6))),
% 0.19/0.47      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (((X0) != (k1_xboole_0))
% 0.19/0.47          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 0.19/0.47          | ((sk_C_2 @ X0 @ X1) = (k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.47  thf('6', plain, (![X10 : $i, X11 : $i]: (v1_relat_1 @ (sk_C_2 @ X10 @ X11))),
% 0.19/0.47      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (((X0) != (k1_xboole_0)) | ((sk_C_2 @ X0 @ X1) = (k1_xboole_0)))),
% 0.19/0.47      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.47  thf('8', plain, (![X1 : $i]: ((sk_C_2 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.47  thf('9', plain, (![X10 : $i, X11 : $i]: (v1_funct_1 @ (sk_C_2 @ X10 @ X11))),
% 0.19/0.47      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 0.19/0.47  thf('10', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.19/0.47      inference('sup+', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf('11', plain, (![X1 : $i]: ((sk_C_2 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (sk_C_2 @ X10 @ X11))),
% 0.19/0.47      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 0.19/0.47  thf('13', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.47      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.19/0.47          | ~ (v1_relat_1 @ X0)
% 0.19/0.47          | ~ (v1_funct_1 @ X0)
% 0.19/0.47          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.19/0.47      inference('demod', [status(thm)], ['2', '10', '13'])).
% 0.19/0.47  thf(t2_boole, axiom,
% 0.19/0.47    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.47  thf(t4_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.47            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.19/0.47          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.47  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.47  thf('18', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.19/0.47      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.47  thf('19', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.19/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.19/0.47          | ~ (v1_funct_1 @ X0)
% 0.19/0.47          | ~ (v1_relat_1 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['14', '19'])).
% 0.19/0.47  thf(t174_funct_1, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.47       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.47          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.19/0.47  thf('21', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('22', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.47  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('24', plain, ((v1_funct_1 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('25', plain, ($false),
% 0.19/0.47      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
