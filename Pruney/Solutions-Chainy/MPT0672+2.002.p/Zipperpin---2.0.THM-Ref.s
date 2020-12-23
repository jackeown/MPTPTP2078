%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A5y3a0hiGr

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 104 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   18
%              Number of atoms          :  549 (1194 expanded)
%              Number of equality atoms :   52 ( 106 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k8_relat_1 @ X9 @ X8 )
        = ( k5_relat_1 @ X8 @ ( k6_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k8_relat_1 @ X9 @ X8 )
        = ( k5_relat_1 @ X8 @ ( k6_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k8_relat_1 @ X9 @ X8 )
        = ( k5_relat_1 @ X8 @ ( k6_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ ( k6_relat_1 @ X15 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t139_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) )
            = ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k8_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k5_relat_1 @ X11 @ ( k8_relat_1 @ X12 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t97_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r1_tarski @ A @ B )
       => ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
            = ( k8_relat_1 @ A @ C ) )
          & ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
            = ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r1_tarski @ A @ B )
         => ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
              = ( k8_relat_1 @ A @ C ) )
            & ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
              = ( k8_relat_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_funct_1])).

thf('15',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k8_relat_1 @ X9 @ X8 )
        = ( k5_relat_1 @ X8 @ ( k6_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['15'])).

thf('26',plain,
    ( ( ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
       != ( k8_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( ( k8_relat_1 @ sk_A @ sk_C )
       != ( k8_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
    = ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['15'])).

thf('34',plain,(
    ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,(
    ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['16','34'])).

thf('36',plain,
    ( ( ( k8_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['20','21'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ( k8_relat_1 @ sk_A @ sk_C )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A5y3a0hiGr
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:36:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 32 iterations in 0.029s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.45  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.45  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.19/0.45  thf(t123_relat_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( v1_relat_1 @ B ) =>
% 0.19/0.45       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.19/0.45  thf('0', plain,
% 0.19/0.45      (![X8 : $i, X9 : $i]:
% 0.19/0.45         (((k8_relat_1 @ X9 @ X8) = (k5_relat_1 @ X8 @ (k6_relat_1 @ X9)))
% 0.19/0.45          | ~ (v1_relat_1 @ X8))),
% 0.19/0.45      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (![X8 : $i, X9 : $i]:
% 0.19/0.45         (((k8_relat_1 @ X9 @ X8) = (k5_relat_1 @ X8 @ (k6_relat_1 @ X9)))
% 0.19/0.45          | ~ (v1_relat_1 @ X8))),
% 0.19/0.45      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      (![X8 : $i, X9 : $i]:
% 0.19/0.45         (((k8_relat_1 @ X9 @ X8) = (k5_relat_1 @ X8 @ (k6_relat_1 @ X9)))
% 0.19/0.45          | ~ (v1_relat_1 @ X8))),
% 0.19/0.45      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.19/0.45  thf(t43_funct_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.19/0.45       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.45  thf('3', plain,
% 0.19/0.45      (![X15 : $i, X16 : $i]:
% 0.19/0.45         ((k5_relat_1 @ (k6_relat_1 @ X16) @ (k6_relat_1 @ X15))
% 0.19/0.45           = (k6_relat_1 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.19/0.45  thf('4', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]:
% 0.19/0.45         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.19/0.45            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.19/0.45          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.45      inference('sup+', [status(thm)], ['2', '3'])).
% 0.19/0.45  thf(fc3_funct_1, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.45       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.45  thf('5', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.19/0.45      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.45  thf('6', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]:
% 0.19/0.45         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.19/0.45           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.45      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.45  thf(t139_relat_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( v1_relat_1 @ B ) =>
% 0.19/0.45       ( ![C:$i]:
% 0.19/0.45         ( ( v1_relat_1 @ C ) =>
% 0.19/0.45           ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) =
% 0.19/0.45             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.19/0.45  thf('7', plain,
% 0.19/0.45      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X10)
% 0.19/0.45          | ((k8_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X10))
% 0.19/0.45              = (k5_relat_1 @ X11 @ (k8_relat_1 @ X12 @ X10)))
% 0.19/0.45          | ~ (v1_relat_1 @ X11))),
% 0.19/0.45      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.19/0.45  thf('8', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         (((k8_relat_1 @ X1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.19/0.45            = (k5_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 0.19/0.45          | ~ (v1_relat_1 @ X2)
% 0.19/0.45          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.45      inference('sup+', [status(thm)], ['6', '7'])).
% 0.19/0.45  thf('9', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.19/0.45      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.45  thf('10', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         (((k8_relat_1 @ X1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.19/0.45            = (k5_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 0.19/0.45          | ~ (v1_relat_1 @ X2))),
% 0.19/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.45  thf('11', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.19/0.45            = (k5_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X2 @ X1))))
% 0.19/0.45          | ~ (v1_relat_1 @ X0)
% 0.19/0.45          | ~ (v1_relat_1 @ X0))),
% 0.19/0.45      inference('sup+', [status(thm)], ['1', '10'])).
% 0.19/0.45  thf('12', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X0)
% 0.19/0.45          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.19/0.45              = (k5_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X2 @ X1)))))),
% 0.19/0.45      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.45  thf('13', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.19/0.45            = (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 0.19/0.45          | ~ (v1_relat_1 @ X0)
% 0.19/0.45          | ~ (v1_relat_1 @ X0))),
% 0.19/0.45      inference('sup+', [status(thm)], ['0', '12'])).
% 0.19/0.45  thf('14', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X0)
% 0.19/0.45          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.19/0.45              = (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 0.19/0.45      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.45  thf(t97_funct_1, conjecture,
% 0.19/0.45    (![A:$i,B:$i,C:$i]:
% 0.19/0.45     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.45       ( ( r1_tarski @ A @ B ) =>
% 0.19/0.45         ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.19/0.45             ( k8_relat_1 @ A @ C ) ) & 
% 0.19/0.45           ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.19/0.45             ( k8_relat_1 @ A @ C ) ) ) ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.45        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.45          ( ( r1_tarski @ A @ B ) =>
% 0.19/0.45            ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.19/0.45                ( k8_relat_1 @ A @ C ) ) & 
% 0.19/0.45              ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.19/0.45                ( k8_relat_1 @ A @ C ) ) ) ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t97_funct_1])).
% 0.19/0.45  thf('15', plain,
% 0.19/0.45      ((((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.45          != (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.45        | ((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.19/0.45            != (k8_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('16', plain,
% 0.19/0.45      ((((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.19/0.45          != (k8_relat_1 @ sk_A @ sk_C)))
% 0.19/0.45         <= (~
% 0.19/0.45             (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.19/0.45                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.19/0.45      inference('split', [status(esa)], ['15'])).
% 0.19/0.45  thf('17', plain,
% 0.19/0.45      (![X8 : $i, X9 : $i]:
% 0.19/0.45         (((k8_relat_1 @ X9 @ X8) = (k5_relat_1 @ X8 @ (k6_relat_1 @ X9)))
% 0.19/0.45          | ~ (v1_relat_1 @ X8))),
% 0.19/0.45      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.19/0.45  thf('18', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t28_xboole_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.45  thf('19', plain,
% 0.19/0.45      (![X2 : $i, X3 : $i]:
% 0.19/0.45         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.19/0.45      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.45  thf('20', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.19/0.45      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.45  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.45    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.45  thf('21', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.45  thf('22', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.19/0.45      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.45  thf('23', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X0)
% 0.19/0.45          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.19/0.45              = (k5_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X2 @ X1)))))),
% 0.19/0.45      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.45  thf('24', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.19/0.45            = (k5_relat_1 @ X0 @ (k6_relat_1 @ sk_A)))
% 0.19/0.45          | ~ (v1_relat_1 @ X0))),
% 0.19/0.45      inference('sup+', [status(thm)], ['22', '23'])).
% 0.19/0.45  thf('25', plain,
% 0.19/0.45      ((((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.45          != (k8_relat_1 @ sk_A @ sk_C)))
% 0.19/0.45         <= (~
% 0.19/0.45             (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.45                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.19/0.45      inference('split', [status(esa)], ['15'])).
% 0.19/0.45  thf('26', plain,
% 0.19/0.45      (((((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A))
% 0.19/0.45           != (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.45         | ~ (v1_relat_1 @ sk_C)))
% 0.19/0.45         <= (~
% 0.19/0.45             (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.45                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.19/0.45      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.45  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('28', plain,
% 0.19/0.45      ((((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A))
% 0.19/0.45          != (k8_relat_1 @ sk_A @ sk_C)))
% 0.19/0.45         <= (~
% 0.19/0.45             (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.45                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.19/0.45      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.45  thf('29', plain,
% 0.19/0.45      (((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.45         | ~ (v1_relat_1 @ sk_C)))
% 0.19/0.45         <= (~
% 0.19/0.45             (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.45                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.19/0.45      inference('sup-', [status(thm)], ['17', '28'])).
% 0.19/0.45  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('31', plain,
% 0.19/0.45      ((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C)))
% 0.19/0.45         <= (~
% 0.19/0.45             (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.45                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.19/0.45      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.45  thf('32', plain,
% 0.19/0.45      ((((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.45          = (k8_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.45      inference('simplify', [status(thm)], ['31'])).
% 0.19/0.45  thf('33', plain,
% 0.19/0.45      (~
% 0.19/0.45       (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.19/0.45          = (k8_relat_1 @ sk_A @ sk_C))) | 
% 0.19/0.45       ~
% 0.19/0.45       (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.45          = (k8_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.45      inference('split', [status(esa)], ['15'])).
% 0.19/0.45  thf('34', plain,
% 0.19/0.45      (~
% 0.19/0.45       (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.19/0.45          = (k8_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.45      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 0.19/0.45  thf('35', plain,
% 0.19/0.45      (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.19/0.45         != (k8_relat_1 @ sk_A @ sk_C))),
% 0.19/0.45      inference('simpl_trail', [status(thm)], ['16', '34'])).
% 0.19/0.45  thf('36', plain,
% 0.19/0.45      ((((k8_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.19/0.45          != (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.45        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.45      inference('sup-', [status(thm)], ['14', '35'])).
% 0.19/0.45  thf('37', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.45  thf('38', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.19/0.45      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.45  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('40', plain,
% 0.19/0.45      (((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))),
% 0.19/0.45      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.19/0.45  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
