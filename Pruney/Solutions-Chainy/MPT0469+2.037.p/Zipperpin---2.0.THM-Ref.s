%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MMrOOVYRJn

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 210 expanded)
%              Number of leaves         :   26 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :  353 (1388 expanded)
%              Number of equality atoms :   42 ( 126 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X46: $i,X49: $i] :
      ( ( X49
        = ( k1_relat_1 @ X46 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X49 @ X46 ) @ ( sk_D_1 @ X49 @ X46 ) ) @ X46 )
      | ( r2_hidden @ ( sk_C_2 @ X49 @ X46 ) @ X49 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X7 ) ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('8',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('9',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('12',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('14',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) )).

thf('16',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X51 ) @ ( k1_relat_1 @ X51 ) )
      | ~ ( r2_hidden @ X52 @ ( k2_relat_1 @ X51 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_3 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('24',plain,(
    ! [X41: $i] :
      ( ( v1_relat_1 @ X41 )
      | ( r2_hidden @ ( sk_B_1 @ X41 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('25',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('26',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','23','26'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('28',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('31',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('32',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('39',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['37','38'])).

thf('40',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','39'])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MMrOOVYRJn
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:55:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 186 iterations in 0.088s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(sk_C_3_type, type, sk_C_3: $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(d4_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X46 : $i, X49 : $i]:
% 0.21/0.52         (((X49) = (k1_relat_1 @ X46))
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ (sk_C_2 @ X49 @ X46) @ (sk_D_1 @ X49 @ X46)) @ X46)
% 0.21/0.52          | (r2_hidden @ (sk_C_2 @ X49 @ X46) @ X49))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.52  thf(t2_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.52  thf(t12_setfam_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X37 : $i, X38 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X8 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X8 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf(t4_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.21/0.52          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X37 : $i, X38 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X6 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X7)))
% 0.21/0.52          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.52  thf('8', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.21/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.52  thf('9', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.52          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '9'])).
% 0.21/0.52  thf('11', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('12', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.52          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '9'])).
% 0.21/0.52  thf('14', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.52          | ((X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf(t19_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 0.21/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X51 : $i, X52 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_C_3 @ X51) @ (k1_relat_1 @ X51))
% 0.21/0.52          | ~ (r2_hidden @ X52 @ (k2_relat_1 @ X51))
% 0.21/0.52          | ~ (v1_relat_1 @ X51))),
% 0.21/0.52      inference('cnf', [status(esa)], [t19_relat_1])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r2_hidden @ (sk_C_3 @ X0) @ (k1_relat_1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf(d1_xboole_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.52        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.52        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('22', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf(d1_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) <=>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.52              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X41 : $i]: ((v1_relat_1 @ X41) | (r2_hidden @ (sk_B_1 @ X41) @ X41))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.21/0.52  thf('25', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('26', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.52  thf('27', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '23', '26'])).
% 0.21/0.52  thf(t60_relat_1, conjecture,
% 0.21/0.52    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.52     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.52        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.52        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.52         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['28'])).
% 0.21/0.52  thf('30', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf(l13_xboole_0, axiom,
% 0.21/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.52         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['28'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (((k1_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.21/0.52         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.21/0.52         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '33'])).
% 0.21/0.52  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.52         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.52  thf('37', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.21/0.52       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.52      inference('split', [status(esa)], ['28'])).
% 0.21/0.52  thf('39', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf('40', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['29', '39'])).
% 0.21/0.52  thf('41', plain, ($false),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['27', '40'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
