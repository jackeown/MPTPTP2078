%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wyQC2MnhPp

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:46 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 165 expanded)
%              Number of leaves         :   20 (  56 expanded)
%              Depth                    :   19
%              Number of atoms          :  487 (1241 expanded)
%              Number of equality atoms :   42 ( 140 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X15 @ X13 @ X14 ) @ ( sk_E @ X15 @ X13 @ X14 ) ) @ X15 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X15 @ X13 @ X14 ) @ ( sk_E @ X15 @ X13 @ X14 ) ) @ X13 )
      | ( X15
        = ( k5_relat_1 @ X14 @ X13 ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( X1
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 ) @ X1 )
      | ( X1
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X15 @ X13 @ X14 ) @ ( sk_E @ X15 @ X13 @ X14 ) ) @ X15 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X15 @ X13 @ X14 ) @ ( sk_F @ X15 @ X13 @ X14 ) ) @ X14 )
      | ( X15
        = ( k5_relat_1 @ X14 @ X13 ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['10'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','16'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['10'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','16'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('31',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('36',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['34','35'])).

thf('37',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['20','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_C @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','16'])).

thf('43',plain,(
    r2_hidden @ ( sk_C @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['10'])).

thf('45',plain,(
    $false ),
    inference('sup-',[status(thm)],['43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wyQC2MnhPp
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:17:18 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.90/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.12  % Solved by: fo/fo7.sh
% 0.90/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.12  % done 856 iterations in 0.678s
% 0.90/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.12  % SZS output start Refutation
% 0.90/1.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.12  thf(sk_C_type, type, sk_C: $i > $i).
% 0.90/1.12  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.12  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.90/1.12  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.90/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.12  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.90/1.12  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.90/1.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.12  thf(d8_relat_1, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( v1_relat_1 @ A ) =>
% 0.90/1.12       ( ![B:$i]:
% 0.90/1.12         ( ( v1_relat_1 @ B ) =>
% 0.90/1.12           ( ![C:$i]:
% 0.90/1.12             ( ( v1_relat_1 @ C ) =>
% 0.90/1.12               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.90/1.12                 ( ![D:$i,E:$i]:
% 0.90/1.12                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.90/1.12                     ( ?[F:$i]:
% 0.90/1.12                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.90/1.12                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.12  thf('0', plain,
% 0.90/1.12      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.90/1.12         (~ (v1_relat_1 @ X13)
% 0.90/1.12          | (r2_hidden @ 
% 0.90/1.12             (k4_tarski @ (sk_D_1 @ X15 @ X13 @ X14) @ (sk_E @ X15 @ X13 @ X14)) @ 
% 0.90/1.12             X15)
% 0.90/1.12          | (r2_hidden @ 
% 0.90/1.12             (k4_tarski @ (sk_F @ X15 @ X13 @ X14) @ (sk_E @ X15 @ X13 @ X14)) @ 
% 0.90/1.12             X13)
% 0.90/1.12          | ((X15) = (k5_relat_1 @ X14 @ X13))
% 0.90/1.12          | ~ (v1_relat_1 @ X15)
% 0.90/1.12          | ~ (v1_relat_1 @ X14))),
% 0.90/1.12      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.90/1.12  thf(t7_tarski, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ~( ( r2_hidden @ A @ B ) & 
% 0.90/1.12          ( ![C:$i]:
% 0.90/1.12            ( ~( ( r2_hidden @ C @ B ) & 
% 0.90/1.12                 ( ![D:$i]:
% 0.90/1.12                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.90/1.12  thf('1', plain,
% 0.90/1.12      (![X10 : $i, X11 : $i]:
% 0.90/1.12         (~ (r2_hidden @ X10 @ X11) | (r2_hidden @ (sk_C @ X11) @ X11))),
% 0.90/1.12      inference('cnf', [status(esa)], [t7_tarski])).
% 0.90/1.12  thf('2', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.12         (~ (v1_relat_1 @ X1)
% 0.90/1.12          | ~ (v1_relat_1 @ X0)
% 0.90/1.12          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 0.90/1.12          | (r2_hidden @ 
% 0.90/1.12             (k4_tarski @ (sk_F @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 0.90/1.12          | ~ (v1_relat_1 @ X2)
% 0.90/1.12          | (r2_hidden @ (sk_C @ X0) @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.12  thf(t3_boole, axiom,
% 0.90/1.12    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.90/1.12  thf('3', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.90/1.12      inference('cnf', [status(esa)], [t3_boole])).
% 0.90/1.12  thf(t48_xboole_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.90/1.12  thf('4', plain,
% 0.90/1.12      (![X8 : $i, X9 : $i]:
% 0.90/1.12         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.90/1.12           = (k3_xboole_0 @ X8 @ X9))),
% 0.90/1.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.90/1.12  thf('5', plain,
% 0.90/1.12      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.12      inference('sup+', [status(thm)], ['3', '4'])).
% 0.90/1.12  thf(t2_boole, axiom,
% 0.90/1.12    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.90/1.12  thf('6', plain,
% 0.90/1.12      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [t2_boole])).
% 0.90/1.12  thf('7', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.12      inference('demod', [status(thm)], ['5', '6'])).
% 0.90/1.12  thf(d5_xboole_0, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.90/1.12       ( ![D:$i]:
% 0.90/1.12         ( ( r2_hidden @ D @ C ) <=>
% 0.90/1.12           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.90/1.12  thf('8', plain,
% 0.90/1.12      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.12         (~ (r2_hidden @ X4 @ X3)
% 0.90/1.12          | ~ (r2_hidden @ X4 @ X2)
% 0.90/1.12          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.90/1.12      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.12  thf('9', plain,
% 0.90/1.12      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.90/1.12         (~ (r2_hidden @ X4 @ X2)
% 0.90/1.12          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.90/1.12      inference('simplify', [status(thm)], ['8'])).
% 0.90/1.12  thf('10', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['7', '9'])).
% 0.90/1.12  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.90/1.12      inference('condensation', [status(thm)], ['10'])).
% 0.90/1.12  thf('12', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         ((r2_hidden @ (sk_C @ X1) @ X1)
% 0.90/1.12          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.90/1.12          | ((X1) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.90/1.12          | ~ (v1_relat_1 @ X1)
% 0.90/1.12          | ~ (v1_relat_1 @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['2', '11'])).
% 0.90/1.12  thf(t62_relat_1, conjecture,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( v1_relat_1 @ A ) =>
% 0.90/1.12       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.90/1.12         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.90/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.12    (~( ![A:$i]:
% 0.90/1.12        ( ( v1_relat_1 @ A ) =>
% 0.90/1.12          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.90/1.12            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.90/1.12    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.90/1.12  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.12      inference('demod', [status(thm)], ['5', '6'])).
% 0.90/1.12  thf(fc2_relat_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.90/1.12  thf('15', plain,
% 0.90/1.12      (![X23 : $i, X24 : $i]:
% 0.90/1.12         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k4_xboole_0 @ X23 @ X24)))),
% 0.90/1.12      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.90/1.12  thf('16', plain,
% 0.90/1.12      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 0.90/1.12      inference('sup+', [status(thm)], ['14', '15'])).
% 0.90/1.12  thf('17', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.90/1.12      inference('sup-', [status(thm)], ['13', '16'])).
% 0.90/1.12  thf('18', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         ((r2_hidden @ (sk_C @ X1) @ X1)
% 0.90/1.12          | ((X1) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.90/1.12          | ~ (v1_relat_1 @ X1)
% 0.90/1.12          | ~ (v1_relat_1 @ X0))),
% 0.90/1.12      inference('demod', [status(thm)], ['12', '17'])).
% 0.90/1.12  thf('19', plain,
% 0.90/1.12      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.90/1.12        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('20', plain,
% 0.90/1.12      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.90/1.12         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.90/1.12      inference('split', [status(esa)], ['19'])).
% 0.90/1.12  thf('21', plain,
% 0.90/1.12      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.90/1.12         (~ (v1_relat_1 @ X13)
% 0.90/1.12          | (r2_hidden @ 
% 0.90/1.12             (k4_tarski @ (sk_D_1 @ X15 @ X13 @ X14) @ (sk_E @ X15 @ X13 @ X14)) @ 
% 0.90/1.12             X15)
% 0.90/1.12          | (r2_hidden @ 
% 0.90/1.12             (k4_tarski @ (sk_D_1 @ X15 @ X13 @ X14) @ (sk_F @ X15 @ X13 @ X14)) @ 
% 0.90/1.12             X14)
% 0.90/1.12          | ((X15) = (k5_relat_1 @ X14 @ X13))
% 0.90/1.12          | ~ (v1_relat_1 @ X15)
% 0.90/1.12          | ~ (v1_relat_1 @ X14))),
% 0.90/1.12      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.90/1.12  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.90/1.12      inference('condensation', [status(thm)], ['10'])).
% 0.90/1.12  thf('23', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (~ (v1_relat_1 @ X0)
% 0.90/1.12          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.90/1.12          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.90/1.12          | (r2_hidden @ 
% 0.90/1.12             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ 
% 0.90/1.12              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.90/1.12             X0)
% 0.90/1.12          | ~ (v1_relat_1 @ X1))),
% 0.90/1.12      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.12  thf('24', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.90/1.12      inference('sup-', [status(thm)], ['13', '16'])).
% 0.90/1.12  thf('25', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (~ (v1_relat_1 @ X0)
% 0.90/1.12          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.90/1.12          | (r2_hidden @ 
% 0.90/1.12             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ 
% 0.90/1.12              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.90/1.12             X0)
% 0.90/1.12          | ~ (v1_relat_1 @ X1))),
% 0.90/1.12      inference('demod', [status(thm)], ['23', '24'])).
% 0.90/1.12  thf('26', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.90/1.12      inference('condensation', [status(thm)], ['10'])).
% 0.90/1.12  thf('27', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         (~ (v1_relat_1 @ X0)
% 0.90/1.12          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.90/1.12          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['25', '26'])).
% 0.90/1.12  thf('28', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.90/1.12      inference('sup-', [status(thm)], ['13', '16'])).
% 0.90/1.12  thf('29', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         (~ (v1_relat_1 @ X0)
% 0.90/1.12          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.90/1.12      inference('demod', [status(thm)], ['27', '28'])).
% 0.90/1.12  thf('30', plain,
% 0.90/1.12      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.90/1.12         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.90/1.12      inference('split', [status(esa)], ['19'])).
% 0.90/1.12  thf('31', plain,
% 0.90/1.12      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.90/1.12         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['29', '30'])).
% 0.90/1.12  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('33', plain,
% 0.90/1.12      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.90/1.12         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.90/1.12      inference('demod', [status(thm)], ['31', '32'])).
% 0.90/1.12  thf('34', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.90/1.12      inference('simplify', [status(thm)], ['33'])).
% 0.90/1.12  thf('35', plain,
% 0.90/1.12      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.90/1.12       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.90/1.12      inference('split', [status(esa)], ['19'])).
% 0.90/1.12  thf('36', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.90/1.12      inference('sat_resolution*', [status(thm)], ['34', '35'])).
% 0.90/1.12  thf('37', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.90/1.12      inference('simpl_trail', [status(thm)], ['20', '36'])).
% 0.90/1.12  thf('38', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         (((X0) != (k1_xboole_0))
% 0.90/1.12          | ~ (v1_relat_1 @ sk_A)
% 0.90/1.12          | ~ (v1_relat_1 @ X0)
% 0.90/1.12          | (r2_hidden @ (sk_C @ X0) @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['18', '37'])).
% 0.90/1.12  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('40', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         (((X0) != (k1_xboole_0))
% 0.90/1.12          | ~ (v1_relat_1 @ X0)
% 0.90/1.12          | (r2_hidden @ (sk_C @ X0) @ X0))),
% 0.90/1.12      inference('demod', [status(thm)], ['38', '39'])).
% 0.90/1.12  thf('41', plain,
% 0.90/1.12      (((r2_hidden @ (sk_C @ k1_xboole_0) @ k1_xboole_0)
% 0.90/1.12        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.90/1.12      inference('simplify', [status(thm)], ['40'])).
% 0.90/1.12  thf('42', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.90/1.12      inference('sup-', [status(thm)], ['13', '16'])).
% 0.90/1.12  thf('43', plain, ((r2_hidden @ (sk_C @ k1_xboole_0) @ k1_xboole_0)),
% 0.90/1.12      inference('simplify_reflect+', [status(thm)], ['41', '42'])).
% 0.90/1.12  thf('44', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.90/1.12      inference('condensation', [status(thm)], ['10'])).
% 0.90/1.12  thf('45', plain, ($false), inference('sup-', [status(thm)], ['43', '44'])).
% 0.90/1.12  
% 0.90/1.12  % SZS output end Refutation
% 0.90/1.12  
% 0.90/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
