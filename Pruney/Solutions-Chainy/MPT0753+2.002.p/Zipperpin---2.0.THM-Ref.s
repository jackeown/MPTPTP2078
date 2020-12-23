%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nE7hkH1pmQ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  54 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :  208 ( 366 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10
       != ( k6_relat_1 @ X9 ) )
      | ( ( k1_relat_1 @ X10 )
        = X9 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('6',plain,(
    ! [X9: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X9 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
        = X9 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('9',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ( v5_relat_1 @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

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

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v5_relat_1 @ sk_A @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v5_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_ordinal1 @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ A )
    <=> ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X13: $i] :
      ( ( v5_ordinal1 @ X13 )
      | ~ ( v3_ordinal1 @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d7_ordinal1])).

thf('18',plain,(
    v5_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v5_relat_1 @ sk_A @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','18'])).

thf('20',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nE7hkH1pmQ
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:00:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 32 iterations in 0.018s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.21/0.47  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.47  thf(fc24_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.47       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.47       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.47  thf('0', plain, (![X5 : $i]: (v4_relat_1 @ (k6_relat_1 @ X5) @ X5)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.47  thf(d18_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v4_relat_1 @ X0 @ X1)
% 0.21/0.47          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.47          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf('3', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ X0)),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(t34_funct_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.47       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.21/0.47         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i]:
% 0.21/0.47         (((X10) != (k6_relat_1 @ X9))
% 0.21/0.47          | ((k1_relat_1 @ X10) = (X9))
% 0.21/0.47          | ~ (v1_funct_1 @ X10)
% 0.21/0.47          | ~ (v1_relat_1 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X9 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ (k6_relat_1 @ X9))
% 0.21/0.47          | ~ (v1_funct_1 @ (k6_relat_1 @ X9))
% 0.21/0.47          | ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.47  thf('7', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.47  thf(fc3_funct_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.47       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.47  thf('8', plain, (![X8 : $i]: (v1_funct_1 @ (k6_relat_1 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.47  thf('9', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.21/0.47      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.47  thf('10', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.47      inference('demod', [status(thm)], ['4', '9'])).
% 0.21/0.47  thf(d19_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.21/0.47          | (v5_relat_1 @ X2 @ X3)
% 0.21/0.47          | ~ (v1_relat_1 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf(t46_ordinal1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47       ( ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) =>
% 0.21/0.47         ( ( v1_relat_1 @ A ) & ( v5_relat_1 @ A @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.47           ( v1_funct_1 @ A ) & ( v5_ordinal1 @ A ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47          ( ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) =>
% 0.21/0.47            ( ( v1_relat_1 @ A ) & ( v5_relat_1 @ A @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.47              ( v1_funct_1 @ A ) & ( v5_ordinal1 @ A ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t46_ordinal1])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.47        | ~ (v5_relat_1 @ sk_A @ (k2_relat_1 @ sk_A))
% 0.21/0.47        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.47        | ~ (v5_ordinal1 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain, ((v3_ordinal1 @ (k1_relat_1 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d7_ordinal1, axiom,
% 0.21/0.47    (![A:$i]: ( ( v5_ordinal1 @ A ) <=> ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) ))).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X13 : $i]:
% 0.21/0.47         ((v5_ordinal1 @ X13) | ~ (v3_ordinal1 @ (k1_relat_1 @ X13)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d7_ordinal1])).
% 0.21/0.47  thf('18', plain, ((v5_ordinal1 @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain, (~ (v5_relat_1 @ sk_A @ (k2_relat_1 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '14', '15', '18'])).
% 0.21/0.47  thf('20', plain, (~ (v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '19'])).
% 0.21/0.47  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('22', plain, ($false), inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
