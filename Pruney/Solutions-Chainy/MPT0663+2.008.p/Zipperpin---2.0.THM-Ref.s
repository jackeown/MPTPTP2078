%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E0APOj2lF1

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  79 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  334 ( 647 expanded)
%              Number of equality atoms :   16 (  36 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t71_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
         => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k1_funct_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('6',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) @ X6 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('19',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( r2_hidden @ X37 @ ( k1_relat_1 @ X39 ) )
      | ( r2_hidden @ X37 @ ( k1_relat_1 @ ( k7_relat_1 @ X39 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf(t70_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('24',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X40 @ ( k1_relat_1 @ ( k7_relat_1 @ X41 @ X42 ) ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X41 @ X42 ) @ X40 )
        = ( k1_funct_1 @ X41 @ X40 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_funct_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
    = ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E0APOj2lF1
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 78 iterations in 0.036s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(t71_funct_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.20/0.48         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.20/0.48            ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.20/0.48              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t71_funct_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C_1)))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(t12_setfam_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X35 : $i, X36 : $i]:
% 0.20/0.48         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      ((r2_hidden @ sk_A @ 
% 0.20/0.48        (k1_setfam_1 @ (k2_tarski @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf(t17_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.20/0.48      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X35 : $i, X36 : $i]:
% 0.20/0.48         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7)) @ X6)),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(d3_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.48          | (r2_hidden @ X2 @ X4)
% 0.20/0.48          | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((r2_hidden @ X2 @ X0)
% 0.20/0.48          | ~ (r2_hidden @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((r2_hidden @ sk_A @ 
% 0.20/0.48        (k1_setfam_1 @ (k2_tarski @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X35 : $i, X36 : $i]:
% 0.20/0.48         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X35 : $i, X36 : $i]:
% 0.20/0.48         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.20/0.48           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((r2_hidden @ X2 @ X0)
% 0.20/0.48          | ~ (r2_hidden @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.20/0.48          | (r2_hidden @ X2 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '17'])).
% 0.20/0.48  thf(t86_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ C ) =>
% 0.20/0.48       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.20/0.48         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X37 @ X38)
% 0.20/0.48          | ~ (r2_hidden @ X37 @ (k1_relat_1 @ X39))
% 0.20/0.48          | (r2_hidden @ X37 @ (k1_relat_1 @ (k7_relat_1 @ X39 @ X38)))
% 0.20/0.48          | ~ (v1_relat_1 @ X39))),
% 0.20/0.48      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ sk_C_1)
% 0.20/0.48          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ X0)))
% 0.20/0.48          | ~ (r2_hidden @ sk_A @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ X0)))
% 0.20/0.48          | ~ (r2_hidden @ sk_A @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '22'])).
% 0.20/0.48  thf(t70_funct_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) =>
% 0.20/0.48         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X40 @ (k1_relat_1 @ (k7_relat_1 @ X41 @ X42)))
% 0.20/0.48          | ((k1_funct_1 @ (k7_relat_1 @ X41 @ X42) @ X40)
% 0.20/0.48              = (k1_funct_1 @ X41 @ X40))
% 0.20/0.48          | ~ (v1_funct_1 @ X41)
% 0.20/0.48          | ~ (v1_relat_1 @ X41))),
% 0.20/0.48      inference('cnf', [status(esa)], [t70_funct_1])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.48        | ((k1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B) @ sk_A)
% 0.20/0.48            = (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('27', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (((k1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B) @ sk_A)
% 0.20/0.48         = (k1_funct_1 @ sk_C_1 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (((k1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B) @ sk_A)
% 0.20/0.48         != (k1_funct_1 @ sk_C_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
