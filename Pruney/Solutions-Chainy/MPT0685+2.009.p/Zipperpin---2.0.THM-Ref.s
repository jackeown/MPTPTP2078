%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2lzcVY3B7I

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:08 EST 2020

% Result     : Theorem 3.12s
% Output     : Refutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 127 expanded)
%              Number of leaves         :   23 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  477 (1019 expanded)
%              Number of equality atoms :   41 (  89 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k10_relat_1 @ X25 @ ( k10_relat_1 @ X24 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X28 @ X27 ) )
        = ( k10_relat_1 @ X28 @ ( k1_relat_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X36 ) @ ( k6_relat_1 @ X35 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['8','15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X2 ) @ X0 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X2 ) @ X0 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k10_relat_1 @ X22 @ X23 )
        = ( k10_relat_1 @ X22 @ ( k3_xboole_0 @ ( k2_relat_1 @ X22 ) @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['8','15','16','17'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['8','15','16','17'])).

thf('32',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27','30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k10_relat_1 @ X2 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','33'])).

thf(t139_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t139_funct_1])).

thf('35',plain,(
    ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2lzcVY3B7I
% 0.16/0.38  % Computer   : n018.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 20:57:42 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 3.12/3.30  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.12/3.30  % Solved by: fo/fo7.sh
% 3.12/3.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.12/3.30  % done 2583 iterations in 2.807s
% 3.12/3.30  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.12/3.30  % SZS output start Refutation
% 3.12/3.30  thf(sk_C_type, type, sk_C: $i).
% 3.12/3.30  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.12/3.30  thf(sk_B_type, type, sk_B: $i).
% 3.12/3.30  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.12/3.30  thf(sk_A_type, type, sk_A: $i).
% 3.12/3.30  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.12/3.30  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.12/3.30  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.12/3.30  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.12/3.30  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.12/3.30  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.12/3.30  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.12/3.30  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.12/3.30  thf(t94_relat_1, axiom,
% 3.12/3.30    (![A:$i,B:$i]:
% 3.12/3.30     ( ( v1_relat_1 @ B ) =>
% 3.12/3.30       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 3.12/3.30  thf('0', plain,
% 3.12/3.30      (![X31 : $i, X32 : $i]:
% 3.12/3.30         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 3.12/3.30          | ~ (v1_relat_1 @ X32))),
% 3.12/3.30      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.12/3.30  thf(t181_relat_1, axiom,
% 3.12/3.30    (![A:$i,B:$i]:
% 3.12/3.30     ( ( v1_relat_1 @ B ) =>
% 3.12/3.30       ( ![C:$i]:
% 3.12/3.30         ( ( v1_relat_1 @ C ) =>
% 3.12/3.30           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 3.12/3.30             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 3.12/3.30  thf('1', plain,
% 3.12/3.30      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.12/3.30         (~ (v1_relat_1 @ X24)
% 3.12/3.30          | ((k10_relat_1 @ (k5_relat_1 @ X25 @ X24) @ X26)
% 3.12/3.30              = (k10_relat_1 @ X25 @ (k10_relat_1 @ X24 @ X26)))
% 3.12/3.30          | ~ (v1_relat_1 @ X25))),
% 3.12/3.30      inference('cnf', [status(esa)], [t181_relat_1])).
% 3.12/3.30  thf('2', plain,
% 3.12/3.30      (![X31 : $i, X32 : $i]:
% 3.12/3.30         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 3.12/3.30          | ~ (v1_relat_1 @ X32))),
% 3.12/3.30      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.12/3.30  thf(t71_relat_1, axiom,
% 3.12/3.30    (![A:$i]:
% 3.12/3.30     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.12/3.30       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.12/3.30  thf('3', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 3.12/3.30      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.12/3.30  thf(t182_relat_1, axiom,
% 3.12/3.30    (![A:$i]:
% 3.12/3.30     ( ( v1_relat_1 @ A ) =>
% 3.12/3.30       ( ![B:$i]:
% 3.12/3.30         ( ( v1_relat_1 @ B ) =>
% 3.12/3.30           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 3.12/3.30             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 3.12/3.30  thf('4', plain,
% 3.12/3.30      (![X27 : $i, X28 : $i]:
% 3.12/3.30         (~ (v1_relat_1 @ X27)
% 3.12/3.30          | ((k1_relat_1 @ (k5_relat_1 @ X28 @ X27))
% 3.12/3.30              = (k10_relat_1 @ X28 @ (k1_relat_1 @ X27)))
% 3.12/3.30          | ~ (v1_relat_1 @ X28))),
% 3.12/3.30      inference('cnf', [status(esa)], [t182_relat_1])).
% 3.12/3.30  thf('5', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i]:
% 3.12/3.30         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.12/3.30            = (k10_relat_1 @ X1 @ X0))
% 3.12/3.30          | ~ (v1_relat_1 @ X1)
% 3.12/3.30          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.12/3.30      inference('sup+', [status(thm)], ['3', '4'])).
% 3.12/3.30  thf(fc3_funct_1, axiom,
% 3.12/3.30    (![A:$i]:
% 3.12/3.30     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.12/3.30       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.12/3.30  thf('6', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.12/3.30      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.12/3.30  thf('7', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i]:
% 3.12/3.30         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.12/3.30            = (k10_relat_1 @ X1 @ X0))
% 3.12/3.30          | ~ (v1_relat_1 @ X1))),
% 3.12/3.30      inference('demod', [status(thm)], ['5', '6'])).
% 3.12/3.30  thf('8', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i]:
% 3.12/3.30         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.12/3.30            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 3.12/3.30          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 3.12/3.30          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.12/3.30      inference('sup+', [status(thm)], ['2', '7'])).
% 3.12/3.30  thf('9', plain,
% 3.12/3.30      (![X31 : $i, X32 : $i]:
% 3.12/3.30         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 3.12/3.30          | ~ (v1_relat_1 @ X32))),
% 3.12/3.30      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.12/3.30  thf(t43_funct_1, axiom,
% 3.12/3.30    (![A:$i,B:$i]:
% 3.12/3.30     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 3.12/3.30       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.12/3.30  thf('10', plain,
% 3.12/3.30      (![X35 : $i, X36 : $i]:
% 3.12/3.30         ((k5_relat_1 @ (k6_relat_1 @ X36) @ (k6_relat_1 @ X35))
% 3.12/3.30           = (k6_relat_1 @ (k3_xboole_0 @ X35 @ X36)))),
% 3.12/3.30      inference('cnf', [status(esa)], [t43_funct_1])).
% 3.12/3.30  thf('11', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i]:
% 3.12/3.30         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.12/3.30            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 3.12/3.30          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 3.12/3.30      inference('sup+', [status(thm)], ['9', '10'])).
% 3.12/3.30  thf('12', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.12/3.30      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.12/3.30  thf('13', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i]:
% 3.12/3.30         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.12/3.30           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.12/3.30      inference('demod', [status(thm)], ['11', '12'])).
% 3.12/3.30  thf('14', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 3.12/3.30      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.12/3.30  thf('15', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i]:
% 3.12/3.30         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.12/3.30           = (k3_xboole_0 @ X1 @ X0))),
% 3.12/3.30      inference('sup+', [status(thm)], ['13', '14'])).
% 3.12/3.30  thf('16', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.12/3.30      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.12/3.30  thf('17', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.12/3.30      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.12/3.30  thf('18', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i]:
% 3.12/3.30         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 3.12/3.30      inference('demod', [status(thm)], ['8', '15', '16', '17'])).
% 3.12/3.30  thf('19', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.12/3.30         (((k3_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)
% 3.12/3.30            = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 3.12/3.30          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 3.12/3.30          | ~ (v1_relat_1 @ X1))),
% 3.12/3.30      inference('sup+', [status(thm)], ['1', '18'])).
% 3.12/3.30  thf('20', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.12/3.30      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.12/3.30  thf('21', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.12/3.30         (((k3_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)
% 3.12/3.30            = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 3.12/3.30          | ~ (v1_relat_1 @ X1))),
% 3.12/3.30      inference('demod', [status(thm)], ['19', '20'])).
% 3.12/3.30  thf('22', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.12/3.30         (((k3_xboole_0 @ (k10_relat_1 @ X1 @ X2) @ X0)
% 3.12/3.30            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 3.12/3.30          | ~ (v1_relat_1 @ X1)
% 3.12/3.30          | ~ (v1_relat_1 @ X1))),
% 3.12/3.30      inference('sup+', [status(thm)], ['0', '21'])).
% 3.12/3.30  thf('23', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.12/3.30         (~ (v1_relat_1 @ X1)
% 3.12/3.30          | ((k3_xboole_0 @ (k10_relat_1 @ X1 @ X2) @ X0)
% 3.12/3.30              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)))),
% 3.12/3.30      inference('simplify', [status(thm)], ['22'])).
% 3.12/3.30  thf(t168_relat_1, axiom,
% 3.12/3.30    (![A:$i,B:$i]:
% 3.12/3.30     ( ( v1_relat_1 @ B ) =>
% 3.12/3.30       ( ( k10_relat_1 @ B @ A ) =
% 3.12/3.30         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 3.12/3.30  thf('24', plain,
% 3.12/3.30      (![X22 : $i, X23 : $i]:
% 3.12/3.30         (((k10_relat_1 @ X22 @ X23)
% 3.12/3.30            = (k10_relat_1 @ X22 @ (k3_xboole_0 @ (k2_relat_1 @ X22) @ X23)))
% 3.12/3.30          | ~ (v1_relat_1 @ X22))),
% 3.12/3.30      inference('cnf', [status(esa)], [t168_relat_1])).
% 3.12/3.30  thf('25', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i]:
% 3.12/3.30         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 3.12/3.30      inference('demod', [status(thm)], ['8', '15', '16', '17'])).
% 3.12/3.30  thf('26', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i]:
% 3.12/3.30         (((k3_xboole_0 @ 
% 3.12/3.30            (k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ X1)) @ X0) @ X1)
% 3.12/3.30            = (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.12/3.30          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 3.12/3.30      inference('sup+', [status(thm)], ['24', '25'])).
% 3.12/3.30  thf('27', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 3.12/3.30      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.12/3.30  thf(t17_xboole_1, axiom,
% 3.12/3.30    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 3.12/3.30  thf('28', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 3.12/3.30      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.12/3.30  thf(t28_xboole_1, axiom,
% 3.12/3.30    (![A:$i,B:$i]:
% 3.12/3.30     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.12/3.30  thf('29', plain,
% 3.12/3.30      (![X2 : $i, X3 : $i]:
% 3.12/3.30         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 3.12/3.30      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.12/3.30  thf('30', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i]:
% 3.12/3.30         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 3.12/3.30           = (k3_xboole_0 @ X0 @ X1))),
% 3.12/3.30      inference('sup-', [status(thm)], ['28', '29'])).
% 3.12/3.30  thf('31', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i]:
% 3.12/3.30         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 3.12/3.30      inference('demod', [status(thm)], ['8', '15', '16', '17'])).
% 3.12/3.30  thf('32', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.12/3.30      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.12/3.30  thf('33', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.12/3.30      inference('demod', [status(thm)], ['26', '27', '30', '31', '32'])).
% 3.12/3.30  thf('34', plain,
% 3.12/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.12/3.30         (((k3_xboole_0 @ X1 @ (k10_relat_1 @ X2 @ X0))
% 3.12/3.30            = (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 3.12/3.30          | ~ (v1_relat_1 @ X2))),
% 3.12/3.30      inference('sup+', [status(thm)], ['23', '33'])).
% 3.12/3.30  thf(t139_funct_1, conjecture,
% 3.12/3.30    (![A:$i,B:$i,C:$i]:
% 3.12/3.30     ( ( v1_relat_1 @ C ) =>
% 3.12/3.30       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 3.12/3.30         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 3.12/3.30  thf(zf_stmt_0, negated_conjecture,
% 3.12/3.30    (~( ![A:$i,B:$i,C:$i]:
% 3.12/3.30        ( ( v1_relat_1 @ C ) =>
% 3.12/3.30          ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 3.12/3.30            ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 3.12/3.30    inference('cnf.neg', [status(esa)], [t139_funct_1])).
% 3.12/3.30  thf('35', plain,
% 3.12/3.30      (((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 3.12/3.30         != (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)))),
% 3.12/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.30  thf('36', plain,
% 3.12/3.30      ((((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 3.12/3.30          != (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B))
% 3.12/3.30        | ~ (v1_relat_1 @ sk_C))),
% 3.12/3.30      inference('sup-', [status(thm)], ['34', '35'])).
% 3.12/3.30  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 3.12/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.30  thf('38', plain,
% 3.12/3.30      (((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 3.12/3.30         != (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 3.12/3.30      inference('demod', [status(thm)], ['36', '37'])).
% 3.12/3.30  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 3.12/3.30  
% 3.12/3.30  % SZS output end Refutation
% 3.12/3.30  
% 3.12/3.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
