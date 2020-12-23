%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RzlorASo8S

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:32 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   61 (  87 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  474 ( 740 expanded)
%              Number of equality atoms :   36 (  59 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('0',plain,(
    ! [X32: $i] :
      ( ( ( k5_relat_1 @ X32 @ ( k6_relat_1 @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X38 ) @ ( k6_relat_1 @ X37 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X30: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X29 @ X28 ) )
        = ( k10_relat_1 @ X29 @ ( k1_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X30: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('9',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X26 @ X25 ) @ X27 )
        = ( k10_relat_1 @ X26 @ ( k10_relat_1 @ X25 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) @ X1 )
        = ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) @ X1 )
        = ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X30: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X23 @ X24 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('24',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X35 @ ( k2_relat_1 @ X36 ) )
      | ( ( k9_relat_1 @ X36 @ ( k10_relat_1 @ X36 @ X35 ) )
        = X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X22: $i] :
      ( ( ( k9_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t148_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_funct_1])).

thf('29',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
     != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) )
     != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RzlorASo8S
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:21:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.68  % Solved by: fo/fo7.sh
% 0.49/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.68  % done 262 iterations in 0.210s
% 0.49/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.68  % SZS output start Refutation
% 0.49/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.68  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.49/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.68  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.49/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.68  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.49/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.68  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.49/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.68  thf(t80_relat_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( v1_relat_1 @ A ) =>
% 0.49/0.68       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.49/0.68  thf('0', plain,
% 0.49/0.68      (![X32 : $i]:
% 0.49/0.68         (((k5_relat_1 @ X32 @ (k6_relat_1 @ (k2_relat_1 @ X32))) = (X32))
% 0.49/0.68          | ~ (v1_relat_1 @ X32))),
% 0.49/0.68      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.49/0.68  thf(t43_funct_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.49/0.68       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.49/0.68  thf('1', plain,
% 0.49/0.68      (![X37 : $i, X38 : $i]:
% 0.49/0.68         ((k5_relat_1 @ (k6_relat_1 @ X38) @ (k6_relat_1 @ X37))
% 0.49/0.68           = (k6_relat_1 @ (k3_xboole_0 @ X37 @ X38)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.49/0.68  thf(t71_relat_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.49/0.68       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.49/0.68  thf('2', plain, (![X30 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 0.49/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.49/0.68  thf(t182_relat_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( v1_relat_1 @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( v1_relat_1 @ B ) =>
% 0.49/0.68           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.49/0.68             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.49/0.68  thf('3', plain,
% 0.49/0.68      (![X28 : $i, X29 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X28)
% 0.49/0.68          | ((k1_relat_1 @ (k5_relat_1 @ X29 @ X28))
% 0.49/0.68              = (k10_relat_1 @ X29 @ (k1_relat_1 @ X28)))
% 0.49/0.68          | ~ (v1_relat_1 @ X29))),
% 0.49/0.68      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.49/0.68  thf('4', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.49/0.68            = (k10_relat_1 @ X1 @ X0))
% 0.49/0.68          | ~ (v1_relat_1 @ X1)
% 0.49/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['2', '3'])).
% 0.49/0.68  thf(fc3_funct_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.49/0.68       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.49/0.68  thf('5', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.49/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.49/0.68  thf('6', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.49/0.68            = (k10_relat_1 @ X1 @ X0))
% 0.49/0.68          | ~ (v1_relat_1 @ X1))),
% 0.49/0.68      inference('demod', [status(thm)], ['4', '5'])).
% 0.49/0.68  thf('7', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.49/0.68            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.49/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['1', '6'])).
% 0.49/0.68  thf('8', plain, (![X30 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 0.49/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.49/0.68  thf('9', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.49/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.49/0.68  thf('10', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.49/0.68      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.49/0.68  thf(t181_relat_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( v1_relat_1 @ B ) =>
% 0.49/0.68       ( ![C:$i]:
% 0.49/0.68         ( ( v1_relat_1 @ C ) =>
% 0.49/0.68           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.49/0.68             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.49/0.68  thf('11', plain,
% 0.49/0.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X25)
% 0.49/0.68          | ((k10_relat_1 @ (k5_relat_1 @ X26 @ X25) @ X27)
% 0.49/0.68              = (k10_relat_1 @ X26 @ (k10_relat_1 @ X25 @ X27)))
% 0.49/0.68          | ~ (v1_relat_1 @ X26))),
% 0.49/0.68      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.49/0.68  thf('12', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (((k10_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)) @ X1)
% 0.49/0.68            = (k10_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.49/0.68          | ~ (v1_relat_1 @ X2)
% 0.49/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['10', '11'])).
% 0.49/0.68  thf('13', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.49/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.49/0.68  thf('14', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (((k10_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)) @ X1)
% 0.49/0.68            = (k10_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.49/0.68          | ~ (v1_relat_1 @ X2))),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('15', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((k10_relat_1 @ X0 @ X1)
% 0.49/0.68            = (k10_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))
% 0.49/0.68          | ~ (v1_relat_1 @ X0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['0', '14'])).
% 0.49/0.68  thf('16', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X0)
% 0.49/0.68          | ((k10_relat_1 @ X0 @ X1)
% 0.49/0.68              = (k10_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))))),
% 0.49/0.68      inference('simplify', [status(thm)], ['15'])).
% 0.49/0.68  thf('17', plain, (![X30 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 0.49/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.49/0.68  thf(t167_relat_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( v1_relat_1 @ B ) =>
% 0.49/0.68       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.49/0.68  thf('18', plain,
% 0.49/0.68      (![X23 : $i, X24 : $i]:
% 0.49/0.68         ((r1_tarski @ (k10_relat_1 @ X23 @ X24) @ (k1_relat_1 @ X23))
% 0.49/0.68          | ~ (v1_relat_1 @ X23))),
% 0.49/0.68      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.49/0.68  thf('19', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.49/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['17', '18'])).
% 0.49/0.68  thf('20', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.49/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.49/0.68  thf('21', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.49/0.68      inference('demod', [status(thm)], ['19', '20'])).
% 0.49/0.68  thf('22', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.49/0.68      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.49/0.68  thf('23', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.49/0.68      inference('demod', [status(thm)], ['21', '22'])).
% 0.49/0.68  thf(t147_funct_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.68       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.49/0.68         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.49/0.68  thf('24', plain,
% 0.49/0.68      (![X35 : $i, X36 : $i]:
% 0.49/0.68         (~ (r1_tarski @ X35 @ (k2_relat_1 @ X36))
% 0.49/0.68          | ((k9_relat_1 @ X36 @ (k10_relat_1 @ X36 @ X35)) = (X35))
% 0.49/0.68          | ~ (v1_funct_1 @ X36)
% 0.49/0.68          | ~ (v1_relat_1 @ X36))),
% 0.49/0.68      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.49/0.68  thf('25', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X0)
% 0.49/0.68          | ~ (v1_funct_1 @ X0)
% 0.49/0.68          | ((k9_relat_1 @ X0 @ 
% 0.49/0.68              (k10_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))
% 0.49/0.68              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['23', '24'])).
% 0.49/0.68  thf('26', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.49/0.68            = (k3_xboole_0 @ X0 @ (k2_relat_1 @ X1)))
% 0.49/0.68          | ~ (v1_relat_1 @ X1)
% 0.49/0.68          | ~ (v1_funct_1 @ X1)
% 0.49/0.68          | ~ (v1_relat_1 @ X1))),
% 0.49/0.68      inference('sup+', [status(thm)], ['16', '25'])).
% 0.49/0.68  thf('27', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (v1_funct_1 @ X1)
% 0.49/0.68          | ~ (v1_relat_1 @ X1)
% 0.49/0.68          | ((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.49/0.68              = (k3_xboole_0 @ X0 @ (k2_relat_1 @ X1))))),
% 0.49/0.68      inference('simplify', [status(thm)], ['26'])).
% 0.49/0.68  thf(t146_relat_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( v1_relat_1 @ A ) =>
% 0.49/0.68       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.49/0.68  thf('28', plain,
% 0.49/0.68      (![X22 : $i]:
% 0.49/0.68         (((k9_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (k2_relat_1 @ X22))
% 0.49/0.68          | ~ (v1_relat_1 @ X22))),
% 0.49/0.68      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.49/0.68  thf(t148_funct_1, conjecture,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.68       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.49/0.68         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.49/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.68    (~( ![A:$i,B:$i]:
% 0.49/0.68        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.68          ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.49/0.68            ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )),
% 0.49/0.68    inference('cnf.neg', [status(esa)], [t148_funct_1])).
% 0.49/0.68  thf('29', plain,
% 0.49/0.68      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.49/0.68         != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('30', plain,
% 0.49/0.68      ((((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.49/0.68          != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.49/0.68        | ~ (v1_relat_1 @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.49/0.68  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('32', plain,
% 0.49/0.68      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.49/0.68         != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.49/0.68      inference('demod', [status(thm)], ['30', '31'])).
% 0.49/0.68  thf('33', plain,
% 0.49/0.68      ((((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))
% 0.49/0.68          != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.49/0.68        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['27', '32'])).
% 0.49/0.68  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('36', plain,
% 0.49/0.68      (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))
% 0.49/0.68         != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.49/0.68      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.49/0.68  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.49/0.68  
% 0.49/0.68  % SZS output end Refutation
% 0.49/0.68  
% 0.49/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
