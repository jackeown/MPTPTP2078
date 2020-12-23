%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1bfxQ8Qqjh

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 201 expanded)
%              Number of leaves         :   23 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  485 (1974 expanded)
%              Number of equality atoms :   54 ( 207 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X40 ) @ X41 )
      | ( r2_hidden @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X47 ) @ X48 )
      | ( ( k10_relat_1 @ X47 @ X48 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t142_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
        <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_1])).

thf('5',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('16',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X37 ) @ X39 )
      | ~ ( r2_hidden @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('17',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t174_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('18',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X50 )
      | ~ ( r1_tarski @ X49 @ ( k2_relat_1 @ X50 ) )
      | ( ( k10_relat_1 @ X50 @ X49 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t174_relat_1])).

thf('19',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('24',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43 != X42 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X42 ) )
       != ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('25',plain,(
    ! [X42: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X42 ) @ ( k1_tarski @ X42 ) )
     != ( k1_tarski @ X42 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('28',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('33',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['8','31','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['6','33'])).

thf('35',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('39',plain,(
    ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['8','31'])).

thf('40',plain,(
    ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1bfxQ8Qqjh
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 156 iterations in 0.049s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(l27_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X40 : $i, X41 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ (k1_tarski @ X40) @ X41) | (r2_hidden @ X40 @ X41))),
% 0.21/0.50      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.50  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ X1 @ X2) | ~ (r1_xboole_0 @ X2 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf(t173_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.50         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X47 : $i, X48 : $i]:
% 0.21/0.50         (~ (r1_xboole_0 @ (k2_relat_1 @ X47) @ X48)
% 0.21/0.50          | ((k10_relat_1 @ X47 @ X48) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ X47))),
% 0.21/0.50      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ (k2_relat_1 @ X1))
% 0.21/0.50          | ~ (v1_relat_1 @ X1)
% 0.21/0.50          | ((k10_relat_1 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf(t142_funct_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.21/0.50         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( v1_relat_1 @ B ) =>
% 0.21/0.50          ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.21/0.50            ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t142_funct_1])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.21/0.50        | ~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.21/0.50         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.21/0.50      inference('split', [status(esa)], ['5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.21/0.50        | (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.21/0.50       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['7'])).
% 0.21/0.50  thf(t2_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.50  thf(t100_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X3 @ X4)
% 0.21/0.50           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf(t5_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.50  thf('12', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.50  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.21/0.50         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('split', [status(esa)], ['5'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.21/0.50      inference('split', [status(esa)], ['7'])).
% 0.21/0.50  thf(l1_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X37 : $i, X39 : $i]:
% 0.21/0.50         ((r1_tarski @ (k1_tarski @ X37) @ X39) | ~ (r2_hidden @ X37 @ X39))),
% 0.21/0.50      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (((r1_tarski @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_B)))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf(t174_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.21/0.50            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X49 : $i, X50 : $i]:
% 0.21/0.50         (((X49) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ X50)
% 0.21/0.50          | ~ (r1_tarski @ X49 @ (k2_relat_1 @ X50))
% 0.21/0.50          | ((k10_relat_1 @ X50 @ X49) != (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t174_relat_1])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.21/0.50         | ~ (v1_relat_1 @ sk_B)
% 0.21/0.50         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.21/0.50         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.21/0.50             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.21/0.50             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.50  thf(t20_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.50         ( k1_tarski @ A ) ) <=>
% 0.21/0.50       ( ( A ) != ( B ) ) ))).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X42 : $i, X43 : $i]:
% 0.21/0.50         (((X43) != (X42))
% 0.21/0.50          | ((k4_xboole_0 @ (k1_tarski @ X43) @ (k1_tarski @ X42))
% 0.21/0.50              != (k1_tarski @ X43)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X42 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ (k1_tarski @ X42) @ (k1_tarski @ X42))
% 0.21/0.50           != (k1_tarski @ X42))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A)))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.21/0.50             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['23', '25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.21/0.50             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.21/0.50             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.21/0.50             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.21/0.50             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) | 
% 0.21/0.50       ~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) | 
% 0.21/0.50       (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.21/0.50      inference('split', [status(esa)], ['5'])).
% 0.21/0.50  thf('33', plain, (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['8', '31', '32'])).
% 0.21/0.50  thf('34', plain, (~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['6', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '34'])).
% 0.21/0.50  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0)))
% 0.21/0.50         <= (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('split', [status(esa)], ['7'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['8', '31'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['37', '40'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
