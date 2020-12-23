%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dSaPqU5uGl

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:48 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   54 (  62 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  385 ( 487 expanded)
%              Number of equality atoms :   33 (  40 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('5',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k7_relat_1 @ X39 @ X38 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X38 ) @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X32 @ X31 ) @ X33 )
        = ( k10_relat_1 @ X32 @ ( k10_relat_1 @ X31 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X43 ) @ ( k6_relat_1 @ X42 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('8',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X43 ) @ ( k6_relat_1 @ X42 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('10',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X35 @ X34 ) )
        = ( k10_relat_1 @ X35 @ ( k1_relat_1 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('17',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','18'])).

thf('20',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X1 @ X2 ) @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X1 @ X2 ) @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['4','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dSaPqU5uGl
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:29:25 EST 2020
% 0.18/0.32  % CPUTime    : 
% 0.18/0.32  % Running portfolio for 600 s
% 0.18/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.32  % Number of cores: 8
% 0.18/0.33  % Python version: Python 3.6.8
% 0.18/0.33  % Running in FO mode
% 0.18/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.49  % Solved by: fo/fo7.sh
% 0.18/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.49  % done 73 iterations in 0.055s
% 0.18/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.49  % SZS output start Refutation
% 0.18/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.18/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.18/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.18/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.18/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.18/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.18/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.18/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.18/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.18/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.18/0.49  thf(t175_funct_2, conjecture,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.18/0.49       ( ![B:$i,C:$i]:
% 0.18/0.49         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.18/0.49           ( ( k10_relat_1 @ A @ C ) =
% 0.18/0.49             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.18/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.49    (~( ![A:$i]:
% 0.18/0.49        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.18/0.49          ( ![B:$i,C:$i]:
% 0.18/0.49            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.18/0.49              ( ( k10_relat_1 @ A @ C ) =
% 0.18/0.49                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.18/0.49    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.18/0.49  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(t28_xboole_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.18/0.49  thf('1', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.18/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.18/0.49  thf(t12_setfam_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.18/0.49  thf('2', plain,
% 0.18/0.49      (![X29 : $i, X30 : $i]:
% 0.18/0.49         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.18/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.18/0.49  thf('3', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (((k1_setfam_1 @ (k2_tarski @ X0 @ X1)) = (X0))
% 0.18/0.49          | ~ (r1_tarski @ X0 @ X1))),
% 0.18/0.49      inference('demod', [status(thm)], ['1', '2'])).
% 0.18/0.49  thf('4', plain,
% 0.18/0.49      (((k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.18/0.49         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.18/0.49      inference('sup-', [status(thm)], ['0', '3'])).
% 0.18/0.49  thf(t94_relat_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( v1_relat_1 @ B ) =>
% 0.18/0.49       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.18/0.49  thf('5', plain,
% 0.18/0.49      (![X38 : $i, X39 : $i]:
% 0.18/0.49         (((k7_relat_1 @ X39 @ X38) = (k5_relat_1 @ (k6_relat_1 @ X38) @ X39))
% 0.18/0.49          | ~ (v1_relat_1 @ X39))),
% 0.18/0.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.18/0.49  thf(t181_relat_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( v1_relat_1 @ B ) =>
% 0.18/0.49       ( ![C:$i]:
% 0.18/0.49         ( ( v1_relat_1 @ C ) =>
% 0.18/0.49           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.18/0.49             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.18/0.49  thf('6', plain,
% 0.18/0.49      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.18/0.49         (~ (v1_relat_1 @ X31)
% 0.18/0.49          | ((k10_relat_1 @ (k5_relat_1 @ X32 @ X31) @ X33)
% 0.18/0.49              = (k10_relat_1 @ X32 @ (k10_relat_1 @ X31 @ X33)))
% 0.18/0.49          | ~ (v1_relat_1 @ X32))),
% 0.18/0.49      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.18/0.49  thf(t43_funct_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.18/0.49       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.18/0.49  thf('7', plain,
% 0.18/0.49      (![X42 : $i, X43 : $i]:
% 0.18/0.49         ((k5_relat_1 @ (k6_relat_1 @ X43) @ (k6_relat_1 @ X42))
% 0.18/0.49           = (k6_relat_1 @ (k3_xboole_0 @ X42 @ X43)))),
% 0.18/0.49      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.18/0.49  thf('8', plain,
% 0.18/0.49      (![X29 : $i, X30 : $i]:
% 0.18/0.49         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.18/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.18/0.49  thf('9', plain,
% 0.18/0.49      (![X42 : $i, X43 : $i]:
% 0.18/0.49         ((k5_relat_1 @ (k6_relat_1 @ X43) @ (k6_relat_1 @ X42))
% 0.18/0.49           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X42 @ X43))))),
% 0.18/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.18/0.49  thf(t71_relat_1, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.18/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.18/0.49  thf('10', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 0.18/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.18/0.49  thf(t182_relat_1, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( v1_relat_1 @ A ) =>
% 0.18/0.49       ( ![B:$i]:
% 0.18/0.49         ( ( v1_relat_1 @ B ) =>
% 0.18/0.49           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.18/0.49             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.18/0.49  thf('11', plain,
% 0.18/0.49      (![X34 : $i, X35 : $i]:
% 0.18/0.49         (~ (v1_relat_1 @ X34)
% 0.18/0.49          | ((k1_relat_1 @ (k5_relat_1 @ X35 @ X34))
% 0.18/0.49              = (k10_relat_1 @ X35 @ (k1_relat_1 @ X34)))
% 0.18/0.49          | ~ (v1_relat_1 @ X35))),
% 0.18/0.49      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.18/0.49  thf('12', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.18/0.49            = (k10_relat_1 @ X1 @ X0))
% 0.18/0.49          | ~ (v1_relat_1 @ X1)
% 0.18/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.18/0.49      inference('sup+', [status(thm)], ['10', '11'])).
% 0.18/0.49  thf(fc3_funct_1, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.18/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.18/0.49  thf('13', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.18/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.18/0.49  thf('14', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.18/0.49            = (k10_relat_1 @ X1 @ X0))
% 0.18/0.49          | ~ (v1_relat_1 @ X1))),
% 0.18/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.18/0.49  thf('15', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (((k1_relat_1 @ (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.18/0.49            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.18/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.18/0.49      inference('sup+', [status(thm)], ['9', '14'])).
% 0.18/0.49  thf('16', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 0.18/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.18/0.49  thf('17', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.18/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.18/0.49  thf('18', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.18/0.49           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.18/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.18/0.49  thf('19', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.49         (((k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X1 @ X0) @ X2))
% 0.18/0.49            = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 0.18/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 0.18/0.49          | ~ (v1_relat_1 @ X1))),
% 0.18/0.49      inference('sup+', [status(thm)], ['6', '18'])).
% 0.18/0.49  thf('20', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.18/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.18/0.49  thf('21', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.49         (((k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X1 @ X0) @ X2))
% 0.18/0.49            = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 0.18/0.49          | ~ (v1_relat_1 @ X1))),
% 0.18/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.18/0.49  thf('22', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.49         (((k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X1 @ X2) @ X0))
% 0.18/0.49            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.18/0.49          | ~ (v1_relat_1 @ X1)
% 0.18/0.49          | ~ (v1_relat_1 @ X1))),
% 0.18/0.49      inference('sup+', [status(thm)], ['5', '21'])).
% 0.18/0.49  thf('23', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.49         (~ (v1_relat_1 @ X1)
% 0.18/0.49          | ((k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X1 @ X2) @ X0))
% 0.18/0.49              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)))),
% 0.18/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.18/0.49  thf('24', plain,
% 0.18/0.49      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.18/0.49          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.18/0.49        | ~ (v1_relat_1 @ sk_A))),
% 0.18/0.49      inference('sup+', [status(thm)], ['4', '23'])).
% 0.18/0.49  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('26', plain,
% 0.18/0.49      (((k10_relat_1 @ sk_A @ sk_C)
% 0.18/0.49         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.18/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.18/0.49  thf('27', plain,
% 0.18/0.49      (((k10_relat_1 @ sk_A @ sk_C)
% 0.18/0.49         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('28', plain, ($false),
% 0.18/0.49      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.18/0.49  
% 0.18/0.49  % SZS output end Refutation
% 0.18/0.49  
% 0.18/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
