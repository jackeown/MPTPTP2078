%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fes3RwVF62

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:37 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   43 (  58 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  372 ( 634 expanded)
%              Number of equality atoms :   20 (  34 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t177_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v2_funct_1 @ A )
              & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
           => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
              = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t177_funct_1])).

thf('0',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X4 @ ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ( ( k10_relat_1 @ X5 @ ( k9_relat_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k10_relat_1 @ sk_A @ ( k9_relat_1 @ sk_A @ sk_B ) )
      = sk_B )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k10_relat_1 @ sk_A @ ( k9_relat_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k9_relat_1 @ X2 @ X3 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X2 ) @ X3 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k9_relat_1 @ sk_A @ sk_B ) )
     != sk_B )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ( k10_relat_1 @ sk_A @ ( k9_relat_1 @ sk_A @ sk_B ) )
 != sk_B ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['6','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fes3RwVF62
% 0.16/0.36  % Computer   : n020.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 13:49:37 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 20 iterations in 0.015s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.23/0.49  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.23/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.23/0.49  thf(t177_funct_1, conjecture,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.49       ( ![B:$i]:
% 0.23/0.49         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.23/0.49           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.23/0.49             ( B ) ) ) ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i]:
% 0.23/0.49        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.49          ( ![B:$i]:
% 0.23/0.49            ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.23/0.49              ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.23/0.49                ( B ) ) ) ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t177_funct_1])).
% 0.23/0.49  thf('0', plain, ((r1_tarski @ sk_B @ (k1_relat_1 @ sk_A))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t164_funct_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.49       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.23/0.49         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.23/0.49  thf('1', plain,
% 0.23/0.49      (![X4 : $i, X5 : $i]:
% 0.23/0.49         (~ (r1_tarski @ X4 @ (k1_relat_1 @ X5))
% 0.23/0.49          | ~ (v2_funct_1 @ X5)
% 0.23/0.49          | ((k10_relat_1 @ X5 @ (k9_relat_1 @ X5 @ X4)) = (X4))
% 0.23/0.49          | ~ (v1_funct_1 @ X5)
% 0.23/0.49          | ~ (v1_relat_1 @ X5))),
% 0.23/0.49      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.23/0.49  thf('2', plain,
% 0.23/0.49      ((~ (v1_relat_1 @ sk_A)
% 0.23/0.49        | ~ (v1_funct_1 @ sk_A)
% 0.23/0.49        | ((k10_relat_1 @ sk_A @ (k9_relat_1 @ sk_A @ sk_B)) = (sk_B))
% 0.23/0.49        | ~ (v2_funct_1 @ sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.49  thf('3', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('4', plain, ((v1_funct_1 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('5', plain, ((v2_funct_1 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      (((k10_relat_1 @ sk_A @ (k9_relat_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.23/0.49      inference('demod', [status(thm)], ['2', '3', '4', '5'])).
% 0.23/0.49  thf(fc6_funct_1, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.23/0.49       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.23/0.49         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.23/0.49         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.23/0.49  thf('7', plain,
% 0.23/0.49      (![X1 : $i]:
% 0.23/0.49         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 0.23/0.49          | ~ (v2_funct_1 @ X1)
% 0.23/0.49          | ~ (v1_funct_1 @ X1)
% 0.23/0.49          | ~ (v1_relat_1 @ X1))),
% 0.23/0.49      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.23/0.49  thf(dt_k2_funct_1, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.49       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.23/0.49         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.23/0.49  thf('8', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.49          | ~ (v1_funct_1 @ X0)
% 0.23/0.49          | ~ (v1_relat_1 @ X0))),
% 0.23/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.23/0.49  thf('9', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.49          | ~ (v1_funct_1 @ X0)
% 0.23/0.49          | ~ (v1_relat_1 @ X0))),
% 0.23/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.23/0.49  thf(t65_funct_1, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.49       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.23/0.49  thf('10', plain,
% 0.23/0.49      (![X6 : $i]:
% 0.23/0.49         (~ (v2_funct_1 @ X6)
% 0.23/0.49          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.23/0.49          | ~ (v1_funct_1 @ X6)
% 0.23/0.49          | ~ (v1_relat_1 @ X6))),
% 0.23/0.49      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.23/0.49  thf(t154_funct_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.49       ( ( v2_funct_1 @ B ) =>
% 0.23/0.49         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.23/0.49  thf('11', plain,
% 0.23/0.49      (![X2 : $i, X3 : $i]:
% 0.23/0.49         (~ (v2_funct_1 @ X2)
% 0.23/0.49          | ((k9_relat_1 @ X2 @ X3) = (k10_relat_1 @ (k2_funct_1 @ X2) @ X3))
% 0.23/0.49          | ~ (v1_funct_1 @ X2)
% 0.23/0.49          | ~ (v1_relat_1 @ X2))),
% 0.23/0.49      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.23/0.49  thf('12', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         (((k9_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k10_relat_1 @ X0 @ X1))
% 0.23/0.49          | ~ (v1_relat_1 @ X0)
% 0.23/0.49          | ~ (v1_funct_1 @ X0)
% 0.23/0.49          | ~ (v2_funct_1 @ X0)
% 0.23/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.49          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.23/0.49      inference('sup+', [status(thm)], ['10', '11'])).
% 0.23/0.49  thf('13', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         (~ (v1_relat_1 @ X0)
% 0.23/0.49          | ~ (v1_funct_1 @ X0)
% 0.23/0.49          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.49          | ~ (v2_funct_1 @ X0)
% 0.23/0.49          | ~ (v1_funct_1 @ X0)
% 0.23/0.49          | ~ (v1_relat_1 @ X0)
% 0.23/0.49          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k10_relat_1 @ X0 @ X1)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['9', '12'])).
% 0.23/0.49  thf('14', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         (((k9_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k10_relat_1 @ X0 @ X1))
% 0.23/0.49          | ~ (v2_funct_1 @ X0)
% 0.23/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.49          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.49          | ~ (v1_funct_1 @ X0)
% 0.23/0.49          | ~ (v1_relat_1 @ X0))),
% 0.23/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.23/0.49  thf('15', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         (~ (v1_relat_1 @ X0)
% 0.23/0.49          | ~ (v1_funct_1 @ X0)
% 0.23/0.49          | ~ (v1_relat_1 @ X0)
% 0.23/0.49          | ~ (v1_funct_1 @ X0)
% 0.23/0.49          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.49          | ~ (v2_funct_1 @ X0)
% 0.23/0.49          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k10_relat_1 @ X0 @ X1)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['8', '14'])).
% 0.23/0.50  thf('16', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (((k9_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k10_relat_1 @ X0 @ X1))
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.23/0.50  thf('17', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k10_relat_1 @ X0 @ X1)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['7', '16'])).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (((k9_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k10_relat_1 @ X0 @ X1))
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.23/0.50  thf('19', plain,
% 0.23/0.50      (((k9_relat_1 @ (k2_funct_1 @ sk_A) @ (k9_relat_1 @ sk_A @ sk_B))
% 0.23/0.50         != (sk_B))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('20', plain,
% 0.23/0.50      ((((k10_relat_1 @ sk_A @ (k9_relat_1 @ sk_A @ sk_B)) != (sk_B))
% 0.23/0.50        | ~ (v1_relat_1 @ sk_A)
% 0.23/0.50        | ~ (v1_funct_1 @ sk_A)
% 0.23/0.50        | ~ (v2_funct_1 @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.50  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('22', plain, ((v1_funct_1 @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('23', plain, ((v2_funct_1 @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('24', plain,
% 0.23/0.50      (((k10_relat_1 @ sk_A @ (k9_relat_1 @ sk_A @ sk_B)) != (sk_B))),
% 0.23/0.50      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.23/0.50  thf('25', plain, ($false),
% 0.23/0.50      inference('simplify_reflect-', [status(thm)], ['6', '24'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
