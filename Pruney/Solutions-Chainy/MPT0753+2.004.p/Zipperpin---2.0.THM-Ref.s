%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cKAmjpWC9J

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   48 (  65 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  230 ( 430 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12
       != ( k6_relat_1 @ X11 ) )
      | ( ( k1_relat_1 @ X12 )
        = X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('1',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X11 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
        = X11 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( ( k7_relat_1 @ X5 @ ( k1_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('12',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( v5_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t46_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v3_ordinal1 @ ( k1_relat_1 @ A ) )
       => ( ( v1_relat_1 @ A )
          & ( v5_relat_1 @ A @ ( k2_relat_1 @ A ) )
          & ( v1_funct_1 @ A )
          & ( v5_ordinal1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v3_ordinal1 @ ( k1_relat_1 @ A ) )
         => ( ( v1_relat_1 @ A )
            & ( v5_relat_1 @ A @ ( k2_relat_1 @ A ) )
            & ( v1_funct_1 @ A )
            & ( v5_ordinal1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_ordinal1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v5_relat_1 @ sk_A @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v5_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v3_ordinal1 @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ A )
    <=> ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X15: $i] :
      ( ( v5_ordinal1 @ X15 )
      | ~ ( v3_ordinal1 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d7_ordinal1])).

thf('21',plain,(
    v5_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v5_relat_1 @ sk_A @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','21'])).

thf('23',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cKAmjpWC9J
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:03:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.22/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.45  % Solved by: fo/fo7.sh
% 0.22/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.45  % done 32 iterations in 0.016s
% 0.22/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.45  % SZS output start Refutation
% 0.22/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.45  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.45  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.22/0.45  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.22/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.45  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.45  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.45  thf(t34_funct_1, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.45       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.22/0.45         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.22/0.45           ( ![C:$i]:
% 0.22/0.45             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.22/0.45  thf('0', plain,
% 0.22/0.45      (![X11 : $i, X12 : $i]:
% 0.22/0.45         (((X12) != (k6_relat_1 @ X11))
% 0.22/0.45          | ((k1_relat_1 @ X12) = (X11))
% 0.22/0.45          | ~ (v1_funct_1 @ X12)
% 0.22/0.45          | ~ (v1_relat_1 @ X12))),
% 0.22/0.45      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.22/0.45  thf('1', plain,
% 0.22/0.45      (![X11 : $i]:
% 0.22/0.45         (~ (v1_relat_1 @ (k6_relat_1 @ X11))
% 0.22/0.45          | ~ (v1_funct_1 @ (k6_relat_1 @ X11))
% 0.22/0.45          | ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11)))),
% 0.22/0.45      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.45  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.45  thf('2', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.22/0.45      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.45  thf(fc3_funct_1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.45       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.45  thf('3', plain, (![X10 : $i]: (v1_funct_1 @ (k6_relat_1 @ X10))),
% 0.22/0.45      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.45  thf('4', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.22/0.45      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.22/0.45  thf(t98_relat_1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( v1_relat_1 @ A ) =>
% 0.22/0.45       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.45  thf('5', plain,
% 0.22/0.45      (![X5 : $i]:
% 0.22/0.45         (((k7_relat_1 @ X5 @ (k1_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 0.22/0.45      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.22/0.45  thf('6', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.22/0.45          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.45      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.45  thf('7', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.22/0.45      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.45  thf('8', plain,
% 0.22/0.45      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.22/0.45      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.45  thf(t87_relat_1, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( v1_relat_1 @ B ) =>
% 0.22/0.45       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.22/0.45  thf('9', plain,
% 0.22/0.45      (![X3 : $i, X4 : $i]:
% 0.22/0.45         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X3 @ X4)) @ X4)
% 0.22/0.45          | ~ (v1_relat_1 @ X3))),
% 0.22/0.45      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.22/0.45  thf('10', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         ((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ X0)
% 0.22/0.45          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.45      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.45  thf('11', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.22/0.45      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.22/0.45  thf('12', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.22/0.45      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.45  thf('13', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.22/0.45      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.22/0.45  thf(d19_relat_1, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( v1_relat_1 @ B ) =>
% 0.22/0.45       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.45  thf('14', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         (~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.22/0.45          | (v5_relat_1 @ X0 @ X1)
% 0.22/0.45          | ~ (v1_relat_1 @ X0))),
% 0.22/0.45      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.45  thf('15', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.45  thf(t46_ordinal1, conjecture,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.45       ( ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) =>
% 0.22/0.45         ( ( v1_relat_1 @ A ) & ( v5_relat_1 @ A @ ( k2_relat_1 @ A ) ) & 
% 0.22/0.45           ( v1_funct_1 @ A ) & ( v5_ordinal1 @ A ) ) ) ))).
% 0.22/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.45    (~( ![A:$i]:
% 0.22/0.45        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.45          ( ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) =>
% 0.22/0.45            ( ( v1_relat_1 @ A ) & ( v5_relat_1 @ A @ ( k2_relat_1 @ A ) ) & 
% 0.22/0.45              ( v1_funct_1 @ A ) & ( v5_ordinal1 @ A ) ) ) ) )),
% 0.22/0.45    inference('cnf.neg', [status(esa)], [t46_ordinal1])).
% 0.22/0.45  thf('16', plain,
% 0.22/0.45      ((~ (v1_relat_1 @ sk_A)
% 0.22/0.45        | ~ (v5_relat_1 @ sk_A @ (k2_relat_1 @ sk_A))
% 0.22/0.45        | ~ (v1_funct_1 @ sk_A)
% 0.22/0.45        | ~ (v5_ordinal1 @ sk_A))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('18', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('19', plain, ((v3_ordinal1 @ (k1_relat_1 @ sk_A))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf(d7_ordinal1, axiom,
% 0.22/0.45    (![A:$i]: ( ( v5_ordinal1 @ A ) <=> ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) ))).
% 0.22/0.45  thf('20', plain,
% 0.22/0.45      (![X15 : $i]:
% 0.22/0.45         ((v5_ordinal1 @ X15) | ~ (v3_ordinal1 @ (k1_relat_1 @ X15)))),
% 0.22/0.45      inference('cnf', [status(esa)], [d7_ordinal1])).
% 0.22/0.45  thf('21', plain, ((v5_ordinal1 @ sk_A)),
% 0.22/0.45      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.45  thf('22', plain, (~ (v5_relat_1 @ sk_A @ (k2_relat_1 @ sk_A))),
% 0.22/0.45      inference('demod', [status(thm)], ['16', '17', '18', '21'])).
% 0.22/0.45  thf('23', plain, (~ (v1_relat_1 @ sk_A)),
% 0.22/0.45      inference('sup-', [status(thm)], ['15', '22'])).
% 0.22/0.45  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('25', plain, ($false), inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.45  
% 0.22/0.45  % SZS output end Refutation
% 0.22/0.45  
% 0.22/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
