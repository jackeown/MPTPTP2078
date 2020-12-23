%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VVCvwbwf0n

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 (  76 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  318 ( 537 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,
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

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ ( k1_relat_1 @ X7 ) )
      | ( v5_funct_1 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

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

thf('25',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['26','27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VVCvwbwf0n
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.45  % Solved by: fo/fo7.sh
% 0.22/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.45  % done 31 iterations in 0.013s
% 0.22/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.45  % SZS output start Refutation
% 0.22/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.45  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.45  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.22/0.45  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.22/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.45  thf(cc1_relat_1, axiom,
% 0.22/0.45    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.22/0.45  thf('0', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.22/0.45      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.22/0.45  thf(cc1_funct_1, axiom,
% 0.22/0.45    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.22/0.45  thf('1', plain, (![X6 : $i]: ((v1_funct_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.22/0.45      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.22/0.45  thf(t60_relat_1, axiom,
% 0.22/0.45    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.45     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.45  thf('2', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.45      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.45  thf(d20_funct_1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.45       ( ![B:$i]:
% 0.22/0.45         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.45           ( ( v5_funct_1 @ B @ A ) <=>
% 0.22/0.45             ( ![C:$i]:
% 0.22/0.45               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.45                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.22/0.45  thf('3', plain,
% 0.22/0.45      (![X7 : $i, X8 : $i]:
% 0.22/0.45         (~ (v1_relat_1 @ X7)
% 0.22/0.45          | ~ (v1_funct_1 @ X7)
% 0.22/0.45          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ (k1_relat_1 @ X7))
% 0.22/0.45          | (v5_funct_1 @ X7 @ X8)
% 0.22/0.45          | ~ (v1_funct_1 @ X8)
% 0.22/0.45          | ~ (v1_relat_1 @ X8))),
% 0.22/0.45      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.22/0.45  thf('4', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.22/0.45          | ~ (v1_relat_1 @ X0)
% 0.22/0.45          | ~ (v1_funct_1 @ X0)
% 0.22/0.45          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.22/0.45          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.45          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.45      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.45  thf('5', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.45          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.45          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.22/0.45          | ~ (v1_funct_1 @ X0)
% 0.22/0.45          | ~ (v1_relat_1 @ X0)
% 0.22/0.45          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.22/0.45      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.45  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.45  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.45  thf('7', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.45          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.22/0.45          | ~ (v1_funct_1 @ X0)
% 0.22/0.45          | ~ (v1_relat_1 @ X0)
% 0.22/0.45          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.22/0.45      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.45  thf('8', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.45          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.22/0.45          | ~ (v1_relat_1 @ X0)
% 0.22/0.45          | ~ (v1_funct_1 @ X0)
% 0.22/0.45          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.22/0.45      inference('sup-', [status(thm)], ['0', '7'])).
% 0.22/0.45  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.45  thf('10', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.22/0.45          | ~ (v1_relat_1 @ X0)
% 0.22/0.45          | ~ (v1_funct_1 @ X0)
% 0.22/0.45          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.22/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.45  thf('11', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.22/0.45          | ~ (v1_relat_1 @ X0)
% 0.22/0.45          | ~ (v1_funct_1 @ X0)
% 0.22/0.45          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.22/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.45  thf(t3_xboole_0, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.45            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.45       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.45            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.45  thf('12', plain,
% 0.22/0.45      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.45         (~ (r2_hidden @ X2 @ X0)
% 0.22/0.45          | ~ (r2_hidden @ X2 @ X3)
% 0.22/0.45          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.45      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.45  thf('13', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.22/0.45          | ~ (v1_funct_1 @ X0)
% 0.22/0.45          | ~ (v1_relat_1 @ X0)
% 0.22/0.45          | ~ (r1_xboole_0 @ k1_xboole_0 @ X1)
% 0.22/0.45          | ~ (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X1))),
% 0.22/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.45  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.45  thf('14', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 0.22/0.45      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.45  thf('15', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.45      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.45  thf('16', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.45      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.45  thf('17', plain,
% 0.22/0.45      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.45         (~ (r2_hidden @ X2 @ X0)
% 0.22/0.45          | ~ (r2_hidden @ X2 @ X3)
% 0.22/0.45          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.45      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.45  thf('18', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.45         ((r1_xboole_0 @ X0 @ X1)
% 0.22/0.45          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.22/0.45          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.22/0.45      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.45  thf('19', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         ((r1_xboole_0 @ X0 @ X1)
% 0.22/0.45          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.22/0.45          | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.45      inference('sup-', [status(thm)], ['15', '18'])).
% 0.22/0.45  thf('20', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.45      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.45  thf('21', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.22/0.45      inference('sup-', [status(thm)], ['14', '20'])).
% 0.22/0.45  thf('22', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.22/0.45          | ~ (v1_funct_1 @ X0)
% 0.22/0.45          | ~ (v1_relat_1 @ X0)
% 0.22/0.45          | ~ (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X1))),
% 0.22/0.45      inference('demod', [status(thm)], ['13', '21'])).
% 0.22/0.45  thf('23', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.22/0.45          | ~ (v1_funct_1 @ X0)
% 0.22/0.45          | ~ (v1_relat_1 @ X0)
% 0.22/0.45          | ~ (v1_relat_1 @ X0)
% 0.22/0.45          | ~ (v1_funct_1 @ X0)
% 0.22/0.45          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.22/0.45      inference('sup-', [status(thm)], ['10', '22'])).
% 0.22/0.45  thf('24', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         (~ (v1_relat_1 @ X0)
% 0.22/0.45          | ~ (v1_funct_1 @ X0)
% 0.22/0.45          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.22/0.45      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.45  thf(t174_funct_1, conjecture,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.45       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.22/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.45    (~( ![A:$i]:
% 0.22/0.45        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.45          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.22/0.45    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.22/0.45  thf('25', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('26', plain, ((~ (v1_funct_1 @ sk_A) | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.45      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.45  thf('27', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('29', plain, ($false),
% 0.22/0.45      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.22/0.45  
% 0.22/0.45  % SZS output end Refutation
% 0.22/0.45  
% 0.22/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
